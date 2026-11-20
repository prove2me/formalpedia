-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_fiveQubitMagicStateProtocol_reportedOutput
-- name    : QEC.Distillation.BK05T.fiveQubitMagicStateProtocol_reportedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-17T19:08:29.457931+00:00
-- url     : https://prove2.me/theorems/8e5e2e1d-dd3f-4ba8-9b82-52e21421acb1
-- title:
--   BK05 T: five Qubit Magic State Protocol reported Output
-- statement:
--   The BK05 T construction uses the five Qubit Magic State Protocol reported Output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean#L2691-L2697
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean#L2691-L2697

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open scoped BigOperators ComplexOrder TensorProduct
attribute [local irreducible] fiveQubitPreparedRowScalar
attribute [local irreducible] GaussianInt.toComplex
attribute [local irreducible] arrayTarget

theorem QEC.Distillation.BK05T.fiveQubitMagicStateProtocol_reportedOutput
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitMagicStateProtocol epsilon hzero hone).run.reportedOutput
        (fiveQubitMagicStateProtocol epsilon hzero hone).behavior =
      fiveQubitAcceptedOutput epsilon hzero hone := by sorry
