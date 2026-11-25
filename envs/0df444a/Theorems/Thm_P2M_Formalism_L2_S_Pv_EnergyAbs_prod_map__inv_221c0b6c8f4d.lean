-- Prove2me | Theorems.Thm_P2M_Formalism_L2_S_Pv_EnergyAbs_prod_map__inv_221c0b6c8f4d
-- name    : P2M_Formalism_L2_S_Pv_EnergyAbs_prod_map__inv_221c0b6c8f4d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:10:23.26181+00:00
-- url     : https://prove2.me/theorems/c7bd7297-b603-5942-8d1b-2aa2a6b3c7be
-- title:
--   P2 M Formalism L2 S Pv Energy Abs prod map  inv 221c0b6c8f4d: P2 M Formalism L2 S Pv Energy Abs prod map  inv 221c0b6c8f4d
-- statement:
--   The P2 M Formalism L2 S Pv Energy Abs prod map  inv 221c0b6c8f4d construction uses the P2 M Formalism L2 S Pv Energy Abs prod map  inv 221c0b6c8f4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsInt.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsInt.lean#L115-L120

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

theorem P2M_Formalism_L2_S_Pv_EnergyAbs_prod_map__inv_221c0b6c8f4d {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) :
    μ.prod μ = ((ν.prod μS).prod (ν'.prod μS')).map (Prod.map φinv φinv) := by sorry

alias «Formalism».«L2».«S».«Pv».«EnergyAbs».«prod_map_φinv» := P2M_Formalism_L2_S_Pv_EnergyAbs_prod_map__inv_221c0b6c8f4d
