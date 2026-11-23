-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_TraceFormIndependence_add_conj__a59ed36e9da2
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_TraceFormIndependence_add_conj__a59ed36e9da2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:18.380268+00:00
-- url     : https://prove2.me/theorems/75af39e7-0ecf-4dab-9ba0-1f5f65c1a48b
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Trace Form Independence add conj  a59ed36e9da2: P2 M Reciprocity Theory Chart Restriction G FD Trace Form Independence add conj  a59ed36e9da2
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Trace Form Independence add conj  a59ed36e9da2 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Trace Form Independence add conj  a59ed36e9da2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceFormIndependence.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceFormIndependence.lean#L13-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_TraceFormIndependence_add_conj__a59ed36e9da2 (w : ℂ) : w + conj w = 2 * (w.re : ℂ) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«TraceFormIndependence».«add_conj'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_TraceFormIndependence_add_conj__a59ed36e9da2
