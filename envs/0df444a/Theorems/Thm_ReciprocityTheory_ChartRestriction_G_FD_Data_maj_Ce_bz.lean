-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_Ce_bz
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.maj_Ce_bz
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:12.584836+00:00
-- url     : https://prove2.me/theorems/0ddefdff-6f5f-5f08-9b0a-07ee754ee7df
-- title:
--   Data: maj Ce bz
-- statement:
--   The Data construction uses the maj Ce bz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentSubOneMajorantBound.lean#L62-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentSubOneMajorantBound.lean#L62-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
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
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
variable {x : Frame X.Ψ r} {τ : X.Ψ}
variable {e : Fin r → ℂ} (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ) (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0)
  (hq : X.d2q x τ e ≠ 0) (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ))
include hx he hq hself

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.maj_Ce_bz (C b : ℂ) :
    X.maj x τ (C • e - b • X.d2z x τ e δ) =
      Complex.normSq C * X.maj x τ e + Complex.normSq b * X.maj x τ (X.d2z x τ e δ) := by sorry
