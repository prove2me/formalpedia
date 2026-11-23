-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_wt_nonneg_of_add
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.wt_nonneg_of_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:40.454235+00:00
-- url     : https://prove2.me/theorems/2fbc8081-7229-4a1d-9f77-a5d6ff3a78ca
-- title:
--   Valuation Residue Lemmas: wt nonneg of add
-- statement:
--   The Valuation Residue Lemmas construction uses the wt nonneg of add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L33-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas

theorem ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.wt_nonneg_of_add {a b c : WithTop ℤ} (hb : b ≠ ⊤) (h : a + b = c) (hc : b ≤ c) : 0 ≤ a := by sorry
