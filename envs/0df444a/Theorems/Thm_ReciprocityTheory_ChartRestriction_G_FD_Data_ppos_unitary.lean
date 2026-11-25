-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_unitary
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.ppos_unitary
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:57.508732+00:00
-- url     : https://prove2.me/theorems/ca8e1672-d5e0-4c0e-ac7c-2adef85bd51b
-- title:
--   Data: ppos unitary
-- statement:
--   The Data construction uses the ppos unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnitaryComplementMoveOfIsotropic.lean#L77-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnitaryComplementMoveOfIsotropic.lean#L77-L94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowFixesComplementOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
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
variable (x : Frame X.Ψ r) (τ : X.Ψ) (g : Matrix (Fin r) (Fin r) ℂ)
  (hg : ∀ u w, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g w) = hermC τ.1 X.Gm u w)
include hg

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.ppos_unitary (hx : x ∈ X.dom) (v : Fin r → ℂ) :
    X.ppos (X.lmulC (fun _ => g) x) τ (Matrix.mulVec g v) = Matrix.mulVec g (X.ppos x τ v) := by sorry
