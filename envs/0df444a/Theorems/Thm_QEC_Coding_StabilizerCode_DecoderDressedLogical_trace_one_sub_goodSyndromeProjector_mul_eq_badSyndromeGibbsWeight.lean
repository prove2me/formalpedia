-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_trace_one_sub_goodSyndromeProjector_mul_eq_badSyndromeGibbsWeight
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.trace_one_sub_goodSyndromeProjector_mul_eq_badSyndromeGibbsWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:19:21.638029+00:00
-- url     : https://prove2.me/theorems/1968a01e-9f5e-49fe-bc89-001f931ff45d
-- title:
--   Decoder Dressed Logical: trace one sub good Syndrome Projector mul eq bad Syndrome Gibbs Weight
-- statement:
--   The CLBT mass `Tr ((I - P_good) rho_beta)` is exactly the sum of the Gibbs
--   weights of the bad syndrome sectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L541-L548
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L541-L548

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
open QEC.Coding.StabilizerCode.DecoderDressedLogical
variable {H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)}

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.trace_one_sub_goodSyndromeProjector_mul_eq_badSyndromeGibbsWeight
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι))
    (rhoBeta : DensityOperator (Qubit.QubitRegister ι)) :
    LinearMap.trace Complex (Qubit.QubitRegister ι)
        ((1 - D.goodSyndromeProjector elementaryErrors) * rhoBeta.toOperator) =
      D.badSyndromeGibbsWeight elementaryErrors rhoBeta := by sorry
