-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_FixedPointImaginarySpan_cc_mul___129c75c726f6
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_FixedPointImaginarySpan_cc_mul___129c75c726f6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:51.043346+00:00
-- url     : https://prove2.me/theorems/763aab62-1ea2-44ac-b024-a2e9b9bced3e
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Fixed Point Imaginary Span cc mul   129c75c726f6: P2 M Reciprocity Theory Chart Restriction G FD Fixed Point Imaginary Span cc mul   129c75c726f6
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Fixed Point Imaginary Span cc mul   129c75c726f6 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Fixed Point Imaginary Span cc mul   129c75c726f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FixedPointImaginarySpan.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FixedPointImaginarySpan.lean#L13-L13

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_FixedPointImaginarySpan_cc_mul___129c75c726f6 (x y : E) : cc (x * y) = cc x * cc y := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«FixedPointImaginarySpan».«cc_mul''» := P2M_ReciprocityTheory_ChartRestriction_G_FD_FixedPointImaginarySpan_cc_mul___129c75c726f6
