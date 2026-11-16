-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_Supplement_theorem_11
-- name    : WeakGraphOracles.OneSided.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:30:19.349549+00:00
-- url     : https://prove2.me/theorems/0f243bfb-bfcd-44b9-ae9f-f94fc82e1143
-- title:
--   Theorem 11 (corrected: empty family) — under either obstruction, induced $F$-freeness is two-sided GEN1 testable only for $F=\emptyset$
-- statement:
--   Let $F$ be a finite family of graphs, each connected and without isolated vertices as throughout the paper (Section 1.1). A graph is induced $F$-free when no member of $F$ has an induced copy in it; farness is measured by $\mathrm{dist}_\oplus$. Suppose that no member of $F$ is a complete graph, or that every member of $F$ contains a cycle. Then
--
--   $$\text{induced }F\text{-freeness is two-sided error testable in GEN1}\iff F=\emptyset .$$
--
--   In particular, for every nonempty such $F$, induced $F$-freeness is not testable with two-sided error in GEN1, which is the printed statement. The empty family satisfies both hypotheses vacuously; every graph is induced $\emptyset$-free and the zero-query policy that always accepts is a perfect tester, so the printed statement needs this exception.
--
--   The hypothesis cannot be dropped: induced $\{P_2,K_3\}$-freeness coincides with $P_2$-freeness, which is testable.
--
--   Differences from the source:
--   - correction: under either hypothesis, induced F-freeness is not testable by 2-sided error in GEN1 → under either hypothesis, testable ↔ F = ∅; reason: F = ∅ satisfies both hypotheses vacuously, every graph is induced ∅-free, and always accepting with zero queries is a perfect tester; for nonempty F the printed claim is kept
--   - encoding: members of F: connected graphs without an isolated vertex (Section 1.1); 'complete graph' → EligiblePattern H for every H ∈ F; complete means H.graph = ⊤ on its own vertex set; reason: the standing assumption of Section 1.1 and the meaning of a complete member
--   - encoding: testable: a tester with query complexity independent of n → ∀ ε > 0, ∃ q, ∀ n, ∃ one policy of depth ≤ q correct on every n-vertex graph; reason: Definition 1 and Remark 2: a non-uniform family of testers, one per n, with ε wired in
--   - encoding: G is ε-far from P: its dist⊕ distance to the closest graph of P is at least ε → ε ≤ dist⊕(G, G') for every G' ∈ P on the same labels; reason: same condition (finitely many graphs, the minimum is attained); an empty P makes every graph far, the +∞ convention
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 11 (PDF p. 12), Theorem 11, with the proof sketch and the {P2,K3} remark on the same page; informal version p. 2 (PDF p. 3), Theorem 4

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_models

set_option autoImplicit false

namespace WeakGraphOracles.OneSided.Supplement

/-- Theorem 11 (corrected: empty family), printed p. 11 (PDF p. 12). `F` is a
finite family of eligible patterns (connected, with an edge). If no member of
`F` is complete, or every member of `F` contains a cycle, then induced
`F`-freeness (farness in `dist⊕`) is two-sided error testable in GEN1 iff
`F = ∅`. The empty family satisfies both printed hypotheses vacuously and is
tested perfectly by always accepting; for every nonempty `F` the printed
non-testability holds. -/
theorem theorem_11 (F : Finset Pattern) (hF : ∀ H ∈ F, EligiblePattern H)
    (hobs : (∀ H ∈ F, H.graph ≠ ⊤) ∨ (∀ H ∈ F, ¬ H.graph.IsAcyclic)) :
    GEN1TwoSidedTestable (fun _ G => InducedFree F G)
        (fun ε _ G => DistFar (fun G' => InducedFree F G') ε G) ↔ F = ∅ := by sorry

end WeakGraphOracles.OneSided.Supplement
