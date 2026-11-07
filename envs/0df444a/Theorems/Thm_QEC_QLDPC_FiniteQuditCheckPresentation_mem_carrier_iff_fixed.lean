-- Prove2me | Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_carrier_iff_fixed
-- name    : QEC.QLDPC.FiniteQuditCheckPresentation.mem_carrier_iff_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:54:27.458371+00:00
-- url     : https://prove2.me/theorems/cc9143c0-576d-4233-ab89-1475782f3cf4
-- title:
--   Finite Qudit Check Presentation: mem carrier iff fixed
-- statement:
--   Carrier membership is exactly simultaneous fixation by every global check.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L220-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/FiniteQuditCheckPresentation.lean#L220-L225

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v
open QEC.QLDPC.FiniteQuditCheckPresentation
variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem QEC.QLDPC.FiniteQuditCheckPresentation.mem_carrier_iff_fixed (P : FiniteQuditCheckPresentation ι κ)
    (ψ : Semantics.Qudit.QuditRegister
      (uniformQuditDimensions (ι := ι) P.alphabetSize)) :
    ψ ∈ P.code.carrier ↔
      ∀ checkIndex, (P.checks checkIndex).globalOperator ψ = ψ := by sorry
