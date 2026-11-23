-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_orthogonal_component_apply
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.orthogonal_component_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:27.548963+00:00
-- url     : https://prove2.me/theorems/0e50fdf9-2401-43ee-b776-57ed9e2e952f
-- title:
--   Data: orthogonal component apply
-- statement:
--   The Data construction uses the orthogonal component apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankEqTwoMulHalfDegree.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankEqTwoMulHalfDegree.lean#L39-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.orthogonal_component_apply (z : Frame X.Ψ r) (ξ x : Fin r → E) (τ : X.Ψ) :
    X.ucomp z ξ (X.embV x) τ = Data.emb τ.1 x -
      (X.Hf z τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
        Data.emb τ.1 ξ := by sorry
