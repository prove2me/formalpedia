-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_flowMat_mulVec
-- name    : ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.flowMat_mulVec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:20.059923+00:00
-- url     : https://prove2.me/theorems/69a90089-0a25-4464-bf5e-71a0a8b7ab5d
-- title:
--   Embedding Hermitian Pairs: flow Mat mul Vec
-- statement:
--   The Embedding Hermitian Pairs construction uses the flow Mat mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/EmbeddingHermitianPairs.lean#L114-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/EmbeddingHermitianPairs.lean#L114-L124

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

theorem ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.flowMat_mulVec (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    X.flowMat ξ τ s *ᵥ v = v + ((-(I * X.c τ * s)) * hermC τ.1 X.Gm v (Data.emb τ.1 ξ)) •
      Data.emb τ.1 ξ := by sorry
