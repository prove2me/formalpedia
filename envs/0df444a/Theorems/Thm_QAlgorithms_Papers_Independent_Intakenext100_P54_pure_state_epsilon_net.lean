-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_pure_state_epsilon_net
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.pure_state_epsilon_net
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:36:03.715919+00:00
-- url     : https://prove2.me/theorems/3146d287-4983-4119-be54-f891a717bb95
-- title:
--   Lemma 4: pure-state epsilon net
-- statement:
--   Let $D\ge1$ and $0<\varepsilon\le1$. There is a finite set $\mathcal M$ of normalized vectors in $\mathbb C^D$ with $|\mathcal M|\le(5/\varepsilon)^{2D}$ such that every normalized vector $|\phi\rangle$ has some $|\psi\rangle\in\mathcal M$ satisfying
--
--   $$\|\phi-\psi\|_1\le2\sqrt{1-F(\phi,\psi)}\le2\big\||\phi\rangle-|\psi\rangle\big\|_2\le\varepsilon.$$
--
--   The first norm acts on the difference of rank-one density operators; the last norm acts on vectors. Fidelity is squared Uhlmann fidelity. This single net controls both distances, preserving the entire chain in the source.
--
--   **Formalization Note** The small-error restriction corrects the printed positive-error domain, as explained in HARD.md.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 3, Lemma 4: pure-state epsilon net

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P54

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder NNReal ENNReal

open MeasureTheory ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P54

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

/-- Lemma 4, PDF pp.3,15. Correct the printed eps > 0 to the proof's 0 < eps ≤ 1;
for eps > 5 the printed cardinality upper bound is smaller than one.
The entire density/vector distance chain is retained. -/
theorem pure_state_epsilon_net (D : ℕ) (hD : 0 < D)
    (eps : ℝ) (heps : 0 < eps) (hepsOne : eps ≤ 1) :
    ∃ M : Finset (RSPVector (Fin D)), (M.card : ℝ) ≤ (5 / eps) ^ (2 * D) ∧
      ∀ phi : RSPVector (Fin D), ∃ psi ∈ M,
        traceNorm (pureDensity phi.val - pureDensity psi.val) ≤
          2 * Real.sqrt (1 - fidelity (pureDensity phi.val) (pureDensity psi.val)) ∧
        2 * Real.sqrt (1 - fidelity (pureDensity phi.val) (pureDensity psi.val)) ≤
          2 * ‖phi.val - psi.val‖ ∧ 2 * ‖phi.val - psi.val‖ ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
