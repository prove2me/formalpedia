-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FixedPointImaginarySpan_span_Lc
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan.span_Lc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:49.135302+00:00
-- url     : https://prove2.me/theorems/390fe775-d783-4cbb-a9ce-09e3ab91901d
-- title:
--   Fixed Point Imaginary Span: span Lc
-- statement:
--   The Fixed Point Imaginary Span construction uses the span Lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FixedPointImaginarySpan.lean#L21-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FixedPointImaginarySpan.lean#L21-L98

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
  ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)

theorem ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan.span_Lc (hg : 0 < g) :
    Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)) = ⊤ := by sorry
