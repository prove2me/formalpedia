-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_latTau_snd_ne
-- name    : ReciprocityTheory.ChartRestriction.L1.latTau_snd_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:26.660101+00:00
-- url     : https://prove2.me/theorems/bf90585b-2297-4d52-b520-01672c5c35ad
-- title:
--   L1: lat Tau snd ne
-- statement:
--   The L1 construction uses the lat Tau snd ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLatTau.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLatTau.lean#L10-L11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLatTau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.latTau_snd_ne (L : PeriodPair) : L.ω₂ ≠ 0 := by sorry
