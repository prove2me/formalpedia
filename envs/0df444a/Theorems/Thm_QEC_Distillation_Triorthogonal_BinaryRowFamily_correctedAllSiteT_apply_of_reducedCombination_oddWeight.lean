-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply_of_reducedCombination_oddWeight
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply_of_reducedCombination_oddWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:39:47.404844+00:00
-- url     : https://prove2.me/theorems/d65a03f4-e06f-4850-bc6a-0c1bddb24744
-- title:
--   Binary Row Family: corrected All Site T apply of reduced Combination odd Weight
-- statement:
--   The Binary Row Family construction uses the corrected All Site T apply of reduced Combination odd Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2619-L2633
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2619-L2633

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
universe uO uE uC
open QEC.Distillation.Triorthogonal.BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply_of_reducedCombination_oddWeight
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (psi : Qubit.QubitRegister Col) (bits : Qubit.Bitstring Col)
    (c : Word (ZMod 2) R.ReducedRowIndex)
    (hbits : bitstringWordEquiv Col bits = R.reducedCombination c) :
    R.correctedAllSiteT psi bits =
      OneQubitMagic.phaseAmplitude
        (Real.pi / 4 * (HammingWeight (R.oddCoefficients c) : Real)) *
        psi bits := by sorry
