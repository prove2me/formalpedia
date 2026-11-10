-- Prove2me | Theorems.Thm_PrecDTree_Main_lemma_3_6
-- name    : PrecDTree.Main.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:52:43.549043+00:00
-- url     : https://prove2.me/theorems/0f987be4-42d6-48b7-b7cd-e2dbe8f18b21
-- title:
--   Lemma 3.6 — the f = 1/4 covering optimum on ξ(T) is at most the sepcover length
-- statement:
--   Let $I=(H,T,\preceq)$ be a PCWCDT instance and $C^*$ an optimal solution of f-PCSC on the instance $(U_\xi,\xi(T),\preceq_\xi,f=1/4)$: a precedence-closed family of tests, of minimum size, whose sets $\xi(t)$ cover at least $\frac14|U_\xi|$ hypotheses. Then, for every optimal precedence-closed decision tree $D$ for $I$ and every sepcover $\mathrm{sepc}(D)$,
--   $$|C^*|\ \le\ |\mathrm{sepc}(I)| .$$
--   Together with Observation 3.5 this bounds the covering optimum that Algorithm 1 approximates by $\mathrm{OPT}(I)$.
--
--   Differences from the source:
--   - encoding: each test t ∈ T is a partition of H, and T is a family of m tests → tests are an indexed family T : Fin m → H → ℕ; the blocks of test t are the fibres of T t, restricted to the current hypothesis set; reason: every partition of a finite set is the fibre partition of a labelling by naturals; the instances are the same
--   - reading: I = (H, T, ⪯) is an instance of the problem → hypotheses: ⪯ is a partial order (IsPartialOrderRel), H is nonempty, and every two distinct hypotheses are separated by some test (Identifiable); reason: the standing assumptions of §2 and the domain of the problem: without separation no decision tree exists and OPT is undefined (the proof of Lemma 3.4 uses it explicitly)
--   - reading: sepc(I) = sepc(D) for an optimal D, ties broken arbitrarily (Definition 3.3) → the conclusion holds for every optimal precedence-closed tree D and every sepcover S of D (IsSepcover, every admissible tie-breaking); reason: 'ties broken arbitrarily' means the statement must hold whatever the choice
--   - encoding: a reply subtree's number of leaves (Definition 3.3) → the number of hypotheses of the reply block; reason: the leaves of a decision tree are its hypotheses, one per hypothesis (p. 4: 'we may assume that the set of leaves of D is H')
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 6, Lemma 3.6

import Mathlib
import Definitions.Def_PrecDTree_Main_Sepcover
import Definitions.Def_PrecDTree_Main_Xi

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Lemma 3.6** (p. 6). Let `I = (H, T, ⪯)` be a PCWCDT instance and `C*` an optimal solution of
f-PCSC on `(U_ξ, ξ(T), ⪯_ξ, f = 1/4)`. Then `|C*| ≤ |sepc(I)|`, for every optimal decision tree and
every sepcover of it. -/
theorem lemma_3_6 {m : ℕ} {H : Type} [DecidableEq H] (le : Fin m → Fin m → Prop)
    (T : Fin m → H → ℕ) (Hs : Finset H) (hle : IsPartialOrderRel le) (hid : Identifiable T Hs)
    (hne : Hs.Nonempty) (D : DTree m H) (hD : IsOptimalW le T Hs D) (S : List (Fin m))
    (hS : IsSepcover T Hs D S) (Cstar : Finset (Fin m))
    (hC : IsPCSCOptimal le (xi T Hs) (1 / 4 : ℝ) Cstar) :
    Cstar.card ≤ S.length := by sorry

end PrecDTree.Main
