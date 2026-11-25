-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_unipotent_sub_one_majorant_bound
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.unipotent_sub_one_majorant_bound
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:09.952441+00:00
-- url     : https://prove2.me/theorems/61ca1b9a-8385-4ece-8ee9-5bafc829d3e1
-- title:
--   Data: unipotent sub one majorant bound
-- statement:
--   The Data construction uses the unipotent sub one majorant bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentSubOneMajorantBound.lean#L103-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentSubOneMajorantBound.lean#L103-L193

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.unipotent_sub_one_majorant_bound (hpos : ∀ v, v ≠ 0 → 0 < X.maj x τ v) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hδ : ∀ u, hermC τ.1 X.Gm u e = 0 → hermC τ.1 X.Gm u (X.Jp x τ e) = 0 →
      X.maj x τ (δ u • e) ≤ κ ^ 2 * X.maj x τ u) (v : Fin r → ℂ) :
    X.maj x τ (Matrix.mulVec (X.d2n x τ e δ - 1) v) ≤ (3 * κ) ^ 2 * X.maj x τ v := by sorry
