-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealEmbeddingCharacters_perL_rank
-- name    : ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters.perL_rank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:04.267464+00:00
-- url     : https://prove2.me/theorems/b91756e3-1aed-4025-b44b-b12e23bb8fc1
-- title:
--   Real Embedding Characters: per L rank
-- statement:
--   The Real Embedding Characters construction uses the per L rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealEmbeddingCharacters.lean#L294-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealEmbeddingCharacters.lean#L294-L296

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (la : Wt X.Ψ r)

theorem ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters.perL_rank : Module.finrank ℤ (perL X la) = Fintype.card X.Ψ := by sorry
