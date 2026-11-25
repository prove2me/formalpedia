-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_ImaginaryMajorants_maj_imag_eq
-- name    : ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants.maj_imag_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:50.818806+00:00
-- url     : https://prove2.me/theorems/9adc0058-cbda-48b9-aa1f-216299fca299
-- title:
--   Imaginary Majorants: maj imag eq
-- statement:
--   The Imaginary Majorants construction uses the maj imag eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ImaginaryMajorants.lean#L31-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ImaginaryMajorants.lean#L31-L113

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoostLowerBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ImaginaryMajorants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants
open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants.maj_imag_eq {z : Frame X.Ψ r} (hz : z ∈ X.dom) (ξ : Fin r → E) (b : X.Ψ → ℝ)
    (hy : X.flow ξ (fun τ => I * (b τ : ℂ)) z ∈ X.dom) (τ : X.Ψ)
    (hee : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (he0 : Data.emb τ.1 ξ ≠ 0)
    (hq : 0 < 1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) (w : Fin r → ℂ) :
    X.maj (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ w = X.maj z τ (Matrix.mulVec
      (boost X τ (Data.emb τ.1 ξ) (X.jp z τ (Data.emb τ.1 ξ)) (X.maj z τ (Data.emb τ.1 ξ))
        (Real.sqrt (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)))⁻¹) w) := by sorry
