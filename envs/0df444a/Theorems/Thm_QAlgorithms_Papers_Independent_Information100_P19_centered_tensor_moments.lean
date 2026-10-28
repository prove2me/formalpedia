-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_centered_tensor_moments
-- name    : QAlgorithms.Papers.Independent.Information100.P19.centered_tensor_moments
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:52:31.590585+00:00
-- url     : https://prove2.me/theorems/3e9ed3b0-68c5-4da1-8022-011f346baa60
-- title:
--   Proposition 5.4
-- statement:
--   For every $m\ge1$ there is one coefficient vector in $\mathbb R[S_{4m}\times S_{4m}]$, independent of dimensions and input, evaluating to $r_m(\widetilde X)$ for every Hermitian $X$. In particular,
--   $$r_1(\widetilde X)=\operatorname{Tr}_{(34),(34)}X-2\operatorname{Tr}_{(34),(23)}X+\operatorname{Tr}_{(12),(34)}X.$$
--   All omitted permutation points are fixed, and real parts are understood. This expresses centered moments as homogeneous tensor invariants.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 30, Proposition 5.4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 5.4; arXiv:2609.29471v1, PDF pp.30. -/
theorem centered_tensor_moments (m : ℕ) (hm : 1 ≤ m) :
    (∃ f : TensorCoeff (4*m), ∀ a b, 0<a → 0<b → ∀ X : Bip a b,
      X.IsHermitian → rMoment (centered X) m = tensorEval f X) ∧
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.IsHermitian →
      rMoment (centered X) 1 = (tensorTrace (s34,s34) X).re -
        2*(tensorTrace (s34,s23) X).re + (tensorTrace (s12,s34) X).re) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
