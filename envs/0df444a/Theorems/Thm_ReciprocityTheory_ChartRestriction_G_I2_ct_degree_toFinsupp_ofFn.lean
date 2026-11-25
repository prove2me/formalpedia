-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_degree_toFinsupp_ofFn
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_degree_toFinsupp_ofFn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:29:13.16211+00:00
-- url     : https://prove2.me/theorems/9b141979-69d8-47e6-ad7a-038553de9a54
-- title:
--   I2: ct degree to Finsupp of Fn
-- statement:
--   The I2 construction uses the ct degree to Finsupp of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L216-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L216-L224

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_degree_toFinsupp_ofFn {ι : Type} [DecidableEq ι] (j : ℕ) (v : Fin j → ι) :
    (Multiset.toFinsupp (↑(List.ofFn v) : Multiset ι)).degree = j := by sorry
