-- Prove2me | Theorems.Thm_PrecDTree_Main_observation_3_5
-- name    : PrecDTree.Main.observation_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:52:40.748635+00:00
-- url     : https://prove2.me/theorems/b78a68cc-a2ba-487a-bde7-cf0dd65f6118
-- title:
--   Observation 3.5 — every sepcover of an optimal worst-case tree has length at most OPT
-- statement:
--   Let $I=(H,T,\preceq)$ be a PCWCDT instance: $H$ nonempty, $\preceq$ a partial order on the tests, every two distinct hypotheses separated by a test. For every optimal precedence-closed decision tree $D$ (minimum worst-case cost) and every sepcover $S=\mathrm{sepc}(D)$ obtained by Definition 3.3 under any tie-breaking,
--   $$|\mathrm{sepc}(I)|=|S|\ \le\ \mathrm{OPT}(I).$$
--   The sepcover is the root path to a test node of $D$, so its length is the cost of some hypothesis below it; this is the bridge from the decision tree to the covering instance of Lemma 3.6.
--
--   Differences from the source:
--   - encoding: each test t ∈ T is a partition of H, and T is a family of m tests → tests are an indexed family T : Fin m → H → ℕ; the blocks of test t are the fibres of T t, restricted to the current hypothesis set; reason: every partition of a finite set is the fibre partition of a labelling by naturals; the instances are the same
--   - reading: I = (H, T, ⪯) is an instance of the problem → hypotheses: ⪯ is a partial order (IsPartialOrderRel), H is nonempty, and every two distinct hypotheses are separated by some test (Identifiable); reason: the standing assumptions of §2 and the domain of the problem: without separation no decision tree exists and OPT is undefined (the proof of Lemma 3.4 uses it explicitly)
--   - reading: sepc(I) = sepc(D) for an optimal D, ties broken arbitrarily (Definition 3.3) → the conclusion holds for every optimal precedence-closed tree D and every sepcover S of D (IsSepcover, every admissible tie-breaking); reason: 'ties broken arbitrarily' means the statement must hold whatever the choice
--   - encoding: a reply subtree's number of leaves (Definition 3.3) → the number of hypotheses of the reply block; reason: the leaves of a decision tree are its hypotheses, one per hypothesis (p. 4: 'we may assume that the set of leaves of D is H')
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 6, Observation 3.5

import Mathlib
import Definitions.Def_PrecDTree_Main_Sepcover

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Observation 3.5** (p. 6). For every PCWCDT instance `I`, `|sepc(I)| ≤ OPT(I)`: every
sepcover of every optimal precedence-closed decision tree has length at most `OPT(I)`. -/
theorem observation_3_5 {m : ℕ} {H : Type} [DecidableEq H] (le : Fin m → Fin m → Prop)
    (T : Fin m → H → ℕ) (Hs : Finset H) (hle : IsPartialOrderRel le) (hid : Identifiable T Hs)
    (hne : Hs.Nonempty) (D : DTree m H) (hD : IsOptimalW le T Hs D) (S : List (Fin m))
    (hS : IsSepcover T Hs D S) :
    S.length ≤ optW le T Hs := by sorry

end PrecDTree.Main
