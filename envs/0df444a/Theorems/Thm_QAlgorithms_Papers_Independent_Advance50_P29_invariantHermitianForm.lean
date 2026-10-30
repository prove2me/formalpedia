-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_invariantHermitianForm
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.invariantHermitianForm
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:24:40.845134+00:00
-- url     : https://prove2.me/theorems/182c34d0-5711-488f-aced-c51d15036002
-- title:
--   Appendix A and (19): classification of unitary-invariant Hermitian forms
-- statement:
--   Let $H$ be a positive-dimensional finite complex Hilbert space, and let $b:B(H)\times B(H)\to\mathbb C$ be a Hermitian sesquilinear form, conjugate-linear in its first argument and linear in its second. Assume $b(UVU^\dagger,UWU^\dagger)=b(V,W)$ for every unitary $U$ and all operators $V,W$. Positivity is not assumed. There exist $\alpha,\beta\in\mathbb C$ such that
--
--   $$
--   b(V,W)=\alpha\operatorname{tr}(V^\dagger W)+\beta\operatorname{tr}(V^\dagger)\operatorname{tr}W\quad\text{for all }V,W.
--   $$
--
--   This classifies the invariant form used in the second-moment calculation. Dimension one is included and no uniqueness is asserted.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 19, Appendix A and (19): classification of unitary-invariant Hermitian forms

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)

open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)

open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]

variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]

variable [Fintype L] [DecidableEq L]

/-- PDF pp.12,19–20, (19), Appendix A: classification of all invariant Hermitian forms.
Dimension one is included, with existence and no uniqueness claim for the coefficients. -/
theorem invariantHermitianForm [Nonempty I]
    (b : Matrix I I ℂ → Matrix I I ℂ → ℂ) (hb : HermitianForm b)
    (hinv : ∀ (U : Matrix.unitaryGroup I ℂ) V W,
      b ((U : Matrix I I ℂ) * V * (U : Matrix I I ℂ)ᴴ)
        ((U : Matrix I I ℂ) * W * (U : Matrix I I ℂ)ᴴ) = b V W) :
    ∃ alpha beta : ℂ, ∀ V W,
      b V W = alpha * (Vᴴ * W).trace + beta * (Vᴴ).trace * W.trace := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
