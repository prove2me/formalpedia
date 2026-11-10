-- Prove2me | Theorems.Thm_PrecDTree_Main_lemma_3_1
-- name    : PrecDTree.Main.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:51:55.759647+00:00
-- url     : https://prove2.me/theorems/05c7fc40-c39c-4b45-9bec-9defa6f280e1
-- title:
--   Lemma 3.1 — OPT is monotone under shrinking the hypothesis set (worst and average case)
-- statement:
--   Let $I=(H,T,\preceq)$ and $I'=(H',T,\preceq)$ be two instances of PCACDT or PCWCDT with $H'\subseteq H$, $H'$ nonempty. Then
--   $$\mathrm{OPT}(I')\le\mathrm{OPT}(I)$$
--   for both objectives: the least average-case cost $\sum_h\mathrm{cost}(D,h)$ and the least worst-case cost $\max_h\mathrm{cost}(D,h)$ over precedence-closed decision trees. Here $\preceq$ is a partial order on the tests and every two distinct hypotheses of $H$ are separated by a test (so the same holds for $H'$). This monotonicity is used in Observation 3.7 and Theorem 3.8 to compare the recursive calls of Algorithm 1 with the whole instance.
--
--   Differences from the source:
--   - encoding: each test t ∈ T is a partition of H, and T is a family of m tests → tests are an indexed family T : Fin m → H → ℕ; the blocks of test t are the fibres of T t, restricted to the current hypothesis set; reason: every partition of a finite set is the fibre partition of a labelling by naturals; the instances are the same
--   - reading: I = (H, T, ⪯) is an instance of the problem → hypotheses: ⪯ is a partial order (IsPartialOrderRel), H is nonempty, and every two distinct hypotheses are separated by some test (Identifiable); reason: the standing assumptions of §2 and the domain of the problem: without separation no decision tree exists and OPT is undefined (the proof of Lemma 3.4 uses it explicitly)
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 5, Lemma 3.1

import Mathlib
import Definitions.Def_PrecDTree_Main_DecisionTree

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Lemma 3.1** (p. 5). For instances `I = (H, T, ⪯)` and `I' = (H', T, ⪯)` of PCACDT or PCWCDT
with `H' ⊆ H`, `OPT(I') ≤ OPT(I)`, for both the average-case and the worst-case objective. -/
theorem lemma_3_1 {m : ℕ} {H : Type} [DecidableEq H] (le : Fin m → Fin m → Prop)
    (T : Fin m → H → ℕ) (Hs Hs' : Finset H) (hle : IsPartialOrderRel le)
    (hid : Identifiable T Hs) (hne : Hs'.Nonempty) (hsub : Hs' ⊆ Hs) :
    optA le T Hs' ≤ optA le T Hs ∧ optW le T Hs' ≤ optW le T Hs := by sorry

end PrecDTree.Main
