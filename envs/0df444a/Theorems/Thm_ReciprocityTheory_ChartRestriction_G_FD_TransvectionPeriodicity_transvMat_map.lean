-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TransvectionPeriodicity_transvMat_map
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity.transvMat_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:24:25.786449+00:00
-- url     : https://prove2.me/theorems/b12321f5-6a54-46ab-8b7a-23c38ffc908d
-- title:
--   Transvection Periodicity: transv Mat map
-- statement:
--   The Transvection Periodicity construction uses the transv Mat map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TransvectionPeriodicity.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TransvectionPeriodicity.lean#L77-L82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity.transvMat_map (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ) (α : E) (s : ℂ)
    (hs : τ.1 α = -(I * X.c τ * s)) :
    (transvMat X.Gm ξ α).map τ.1 = X.flowMat ξ τ s := by sorry
