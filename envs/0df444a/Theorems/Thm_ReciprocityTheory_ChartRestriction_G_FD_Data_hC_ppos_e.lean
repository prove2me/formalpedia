-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hC_ppos_e
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.hC_ppos_e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:40.659621+00:00
-- url     : https://prove2.me/theorems/2ef90d2b-578a-4316-9567-99255254dbed
-- title:
--   Data: h C ppos e
-- statement:
--   The Data construction uses the h C ppos e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowFixesComplementOfIsotropic.lean#L102-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowFixesComplementOfIsotropic.lean#L102-L112

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowFixesComplementOfIsotropic
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
variable (ξ : Fin r → E) (τ : X.Ψ)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.hC_ppos_e (x : Frame X.Ψ r) (v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ v) (emb τ.1 ξ) =
      dotProduct (fun b => hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)))
        (Matrix.mulVec (X.gramPos x τ)⁻¹
          (fun a => hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a)) (emb τ.1 ξ))) := by sorry
