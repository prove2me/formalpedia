-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_det_flowMat
-- name    : ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.det_flowMat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:53.916797+00:00
-- url     : https://prove2.me/theorems/bb3f96b1-0576-45d4-920e-f77fa2cd29db
-- title:
--   Embedding Hermitian Pairs: det flow Mat
-- statement:
--   The Embedding Hermitian Pairs construction uses the det flow Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/EmbeddingHermitianPairs.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/EmbeddingHermitianPairs.lean#L95-L99

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.det_flowMat {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ) :
    (X.flowMat ξ τ s).det = 1 := by sorry
