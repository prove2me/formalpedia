-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_wv_dot
-- name    : ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.wv_dot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:46.903056+00:00
-- url     : https://prove2.me/theorems/f5345671-8e71-4f4f-a5c1-8f51a2b3e3b7
-- title:
--   Embedding Hermitian Pairs: wv dot
-- statement:
--   The Embedding Hermitian Pairs construction uses the wv dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/EmbeddingHermitianPairs.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/EmbeddingHermitianPairs.lean#L52-L56

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

theorem ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.wv_dot (ξ : Fin r → E) (τ : X.Ψ) (v : Fin r → ℂ) :
    wv X ξ τ ⬝ᵥ v = hermC τ.1 X.Gm v (Data.emb τ.1 ξ) := by sorry
