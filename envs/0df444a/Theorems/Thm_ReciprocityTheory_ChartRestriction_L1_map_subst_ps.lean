-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_map_subst_ps
-- name    : ReciprocityTheory.ChartRestriction.L1.map_subst_ps
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:43:38.509815+00:00
-- url     : https://prove2.me/theorems/ee9c8b79-35c5-4710-8425-e372b686b2ff
-- title:
--   L1: map subst ps
-- statement:
--   The L1 construction uses the map subst ps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L173-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L173-L176

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K)

theorem ReciprocityTheory.ChartRestriction.L1.map_subst_ps {a : PowerSeries K} (ha : constantCoeff a = 0) (f : PowerSeries K) :
    PowerSeries.map φ (f.subst a) = (PowerSeries.map φ f).subst (PowerSeries.map φ a) := by sorry
