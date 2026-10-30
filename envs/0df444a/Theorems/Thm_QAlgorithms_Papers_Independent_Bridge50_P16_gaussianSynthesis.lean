-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_gaussianSynthesis
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.gaussianSynthesis
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T14:36:36.145826+00:00
-- url     : https://prove2.me/theorems/d6326289-1645-4ee2-8b87-c59ad40fc35d
-- title:
--   Theorem 4, Eq.(7): Gaussian channel synthesis
-- statement:
--   Let $\Phi_1,\Phi_2$ be Gaussian CPTP channels on $n\ge1$ bosonic modes, with real gain matrices $T_j$, symmetric noise matrices $N_j$, and displacement vectors $d_j$. Use interleaved quadratures with $[q_k,p_l]=i\delta_{kl}$ and vacuum covariance $I/2$. Then their composition is the full Gaussian channel with specification
--
--   $$T=T_2T_1,\qquad N=T_2N_1T_2^{\mathsf T}+N_2,\qquad d=T_2d_1+d_2.$$
--
--   The specification is the all-input Weyl characteristic-function law, not only a rule for Gaussian input moments. This gives the channel composition used in subsequent loss/amplifier identities.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 3, Theorem 4, Eq.(7): Gaussian channel synthesis

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P16

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P16

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P32 (CPTP applyChoi)

/-- Theorem 4, PDF p.3 Eq.(7); known result credited to [45] Eq.(26).
All three affine Gaussian parameters are retained on the full multimode channel. -/
theorem gaussianSynthesis {n : ℕ} (hn : 0 < n)
    (E1 E2 : T.Operation (Fin n → ℕ) (Fin n → ℕ))
    (M1 M2 V1 V2 : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (d1 d2 : PhaseIndex n → ℝ)
    (h1 : GaussianSpecification E1 M1 V1 d1)
    (h2 : GaussianSpecification E2 M2 V2 d2) :
    GaussianSpecification (E2 ∘ E1) (M2 * M1)
      (M2 * V1 * M2.transpose + V2) (M2.mulVec d1 + d2) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
