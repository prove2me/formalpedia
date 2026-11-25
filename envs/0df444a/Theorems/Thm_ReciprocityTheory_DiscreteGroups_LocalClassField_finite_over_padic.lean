-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finite_over_padic
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.finite_over_padic
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:01:12.259627+00:00
-- url     : https://prove2.me/theorems/36f4e975-d62d-4e80-b949-a0776d308830
-- title:
--   Local Class Field: finite over padic
-- statement:
--   The Local Class Field construction uses the finite over padic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportA.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportA.lean#L63-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ValuativeRel Function Filter Topology
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.finite_over_padic (p : ℕ) [Fact p.Prime] (f : ℚ_[p] →+* K) (hf : Continuous f) :
    letI := f.toAlgebra
    FiniteDimensional ℚ_[p] K := by sorry
