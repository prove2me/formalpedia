-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_preparation_reductions
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.preparation_reductions
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:00:46.548748+00:00
-- url     : https://prove2.me/theorems/6ba272e7-7839-495a-b979-d62254e4aad0
-- title:
--   Lemma 7: preparations reduce to state monotones
-- statement:
--   Let $\mathcal F$ be a nonempty closed convex family of free density operators. Let $\mathcal O$ be free operations for this state theory: all density-operator preparations are physically allowed and $P_\sigma$ is free exactly when $\sigma\in\mathcal F$. The reverse implication is the proof-used free-state-preservation convention from the trivial free input, while the forward inclusion is printed in the lemma. For any density operator $\rho$, the trivial-input preparation $P_\rho$ satisfies
--   $$
--   R_{\max,\mathcal O}(P_\rho)=R_{\max,\mathcal F}(\rho),\qquad
--   R_{s,\mathcal O}(P_\rho)=R_{s,\mathcal F}(\rho),\qquad
--   R_{\min,\mathcal O}(P_\rho)=R_{\min,\mathcal F}(\rho).
--   $$
--   State robustness uses the same $1+r$ mixture convention, with all density operators as generalized noise and free states as standard noise. State min-resource is the reciprocal maximum free-state support overlap.
--
--   All three reductions exploit the dimension-one input and leave no channel-input optimization at the state level.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 14, Lemma 7: preparations reduce to state monotones

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Lemma 7, PDF pp.13-14 (E1): all THREE preparation/state equalities.
The underlying free-operation convention is explicit; the printed inclusion
alone would incorrectly permit every resourceful preparation to be free. -/
theorem preparation_reductions (O : ResourceTheory) (hO : Regular O)
    (F : ∀ d : ℕ+, Set (Matrix (Fin d) (Fin d) ℂ)) (hF : PreparationTheory O F)
    {d : ℕ+} (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    maximal O (preparationChoi rho) = stateMaximal (F d) rho ∧
    standard O (preparationChoi rho) = stateStandard (F d) rho ∧
    minimum O (preparationChoi rho) = stateMinimum (F d) rho := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
