-- Prove2me | Theorems.Thm_P2M_Formalism_L2_S_Pv_SchurTens_integrable_conj__b586f57a26e4
-- name    : P2M_Formalism_L2_S_Pv_SchurTens_integrable_conj__b586f57a26e4
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:50:55.819513+00:00
-- url     : https://prove2.me/theorems/3a10387e-101a-41f0-b7d7-51570e3358a1
-- title:
--   P2 M Formalism L2 S Pv Schur Tens integrable conj  b586f57a26e4: P2 M Formalism L2 S Pv Schur Tens integrable conj  b586f57a26e4
-- statement:
--   The P2 M Formalism L2 S Pv Schur Tens integrable conj  b586f57a26e4 construction uses the P2 M Formalism L2 S Pv Schur Tens integrable conj  b586f57a26e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensSpan.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensSpan.lean#L24-L26

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {K : Type*} [MeasurableSpace K] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
variable {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}

theorem P2M_Formalism_L2_S_Pv_SchurTens_integrable_conj__b586f57a26e4 {f : K → ℂ} (hf : Integrable f m) : Integrable (fun x => conj (f x)) m := by sorry

alias «Formalism».«L2».«S».«Pv».«SchurTens».«integrable_conj'» := P2M_Formalism_L2_S_Pv_SchurTens_integrable_conj__b586f57a26e4
