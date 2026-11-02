-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_tensorAdditivity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.tensorAdditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:08:58.111847+00:00
-- url     : https://prove2.me/theorems/79b73355-2b1f-4b37-a19a-5fa1a491a8e0
-- title:
--   Tensor-product additivity
-- statement:
--   Let $\rho$ on $A\otimes B$ and $\sigma$ on $A'\otimes B'$ be independent positive semidefinite, trace-one states on arbitrary nonzero finite-dimensional local spaces. Regard their tensor product as bipartite across $AA':BB'$. Let $W$ be the primal SDP (7) value and $E_W=\log_2W$. Then
--
--   $$W(\rho\otimes\sigma)=W(\rho)W(\sigma),\qquad E_W(\rho\otimes\sigma)=E_W(\rho)+E_W(\sigma).$$
--
--   The identities hold without requiring equal local dimensions and allow the bound to be evaluated on tensor powers.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 2, Unnumbered property i): tensor-product additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P83

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P83

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

variable {A B C D : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Property i), PDF pp.2–3: multiplicativity of W and additivity of E_W,
with independent input states and independent local dimensions. -/
theorem tensorAdditivity [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix (C × D) (C × D) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    wValue (regroupedTensor rho sigma) = wValue rho * wValue sigma ∧
    entanglementW (regroupedTensor rho sigma) = entanglementW rho + entanglementW sigma := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
