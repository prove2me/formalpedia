-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_span_embV
-- name    : ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.span_embV
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:47:32.796401+00:00
-- url     : https://prove2.me/theorems/d24cfa47-2701-4349-9d86-8b6b67302d85
-- title:
--   Real Place Embeddings: span emb V
-- statement:
--   The Real Place Embeddings construction uses the span emb V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealPlaceEmbeddings.lean#L183-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealPlaceEmbeddings.lean#L183-L213

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
open NumberField Module Submodule
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.span_embV {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    span ℝ (Set.range fun i => X.embV (g i : Fin r → E)) = ⊤ := by sorry
