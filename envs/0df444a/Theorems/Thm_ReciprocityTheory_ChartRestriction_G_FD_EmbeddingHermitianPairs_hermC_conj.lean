-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_conj
-- name    : ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.hermC_conj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:38.475669+00:00
-- url     : https://prove2.me/theorems/2ec0a9f8-147a-45d8-a996-b52f8be16948
-- title:
--   Embedding Hermitian Pairs: herm C conj
-- statement:
--   The Embedding Hermitian Pairs construction uses the herm C conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/EmbeddingHermitianPairs.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/EmbeddingHermitianPairs.lean#L32-L38

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
variable (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

theorem ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.hermC_conj (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    conj (hermC τ G u v) = hermC τ G v u := by sorry
