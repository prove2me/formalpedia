-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicIndexSums_ucomp_apply
-- name    : ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.ucomp_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:47.88085+00:00
-- url     : https://prove2.me/theorems/94320bed-e7ec-5609-b414-93b98af2814e
-- title:
--   Isotropic Index Sums: ucomp apply
-- statement:
--   The Isotropic Index Sums construction uses the ucomp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicIndexSums.lean#L172-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicIndexSums.lean#L172-L174

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsPerpHermitianReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicIndexSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.ucomp_apply (x : Frame X.Ψ r) (ξ : Fin r → E) (U : X.Ψ → Fin r → ℂ) (τ : X.Ψ) :
    X.ucomp x ξ U τ = U τ - (X.Hf x τ (U τ) (Data.emb τ.1 ξ) /
      X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by sorry
