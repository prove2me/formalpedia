-- Prove2me | Theorems.Thm_P2M_Formalism_L2_S_Pv_EnergyAbs_measurable__inv_e6ee5e712638
-- name    : P2M_Formalism_L2_S_Pv_EnergyAbs_measurable__inv_e6ee5e712638
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:10:16.268441+00:00
-- url     : https://prove2.me/theorems/89aa42c6-ca98-5270-af7f-67c9fe18f958
-- title:
--   P2 M Formalism L2 S Pv Energy Abs measurable  inv e6ee5e712638: P2 M Formalism L2 S Pv Energy Abs measurable  inv e6ee5e712638
-- statement:
--   The P2 M Formalism L2 S Pv Energy Abs measurable  inv e6ee5e712638 construction uses the P2 M Formalism L2 S Pv Energy Abs measurable  inv e6ee5e712638 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsInt.lean#L27-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsInt.lean#L27-L27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem P2M_Formalism_L2_S_Pv_EnergyAbs_measurable__inv_e6ee5e712638 : Measurable (φinv : G × G → G) := by sorry

alias «Formalism».«L2».«S».«Pv».«EnergyAbs».«measurable_φinv» := P2M_Formalism_L2_S_Pv_EnergyAbs_measurable__inv_e6ee5e712638
