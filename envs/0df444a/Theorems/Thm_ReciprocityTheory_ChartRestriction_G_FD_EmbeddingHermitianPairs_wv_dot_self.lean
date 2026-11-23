-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_wv_dot_self
-- name    : ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.wv_dot_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:56.507076+00:00
-- url     : https://prove2.me/theorems/7f1587b8-c985-47d3-8569-7c9b7ff3755c
-- title:
--   Embedding Hermitian Pairs: wv dot self
-- statement:
--   The Embedding Hermitian Pairs construction uses the wv dot self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/EmbeddingHermitianPairs.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/EmbeddingHermitianPairs.lean#L58-L61

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

theorem ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.wv_dot_self {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) :
    wv X ξ τ ⬝ᵥ Data.emb τ.1 ξ = 0 := by sorry
