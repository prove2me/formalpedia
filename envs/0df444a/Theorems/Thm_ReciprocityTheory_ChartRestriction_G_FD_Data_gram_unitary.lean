-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gram_unitary
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.gram_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:44.449905+00:00
-- url     : https://prove2.me/theorems/5c89b679-1e15-4089-92e9-e09886386d57
-- title:
--   Data: gram unitary
-- statement:
--   The Data construction uses the gram unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnitaryComplementMoveOfIsotropic.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnitaryComplementMoveOfIsotropic.lean#L73-L75

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.gram_unitary : gram τ.1 X.Gm (g * mat x τ) = gram τ.1 X.Gm (mat x τ) := by sorry
