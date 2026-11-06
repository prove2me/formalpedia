-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_generatedStabilizer_css_components
-- name    : QEC.Coding.PauliSymplectic.generatedStabilizer_css_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:40:18.875493+00:00
-- url     : https://prove2.me/theorems/a4b153d7-ccc8-4fbd-9918-3a3d90cd95b2
-- title:
--   Pauli Symplectic: generated Stabilizer css components
-- statement:
--   Products and adjoints of dual-contained CSS checks retain trivial phase and
--   their X/Z components remain in the corresponding classical codes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/SourceValidity.lean#L107-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/SourceValidity.lean#L107-L144

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.generatedStabilizer_css_components
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι)
    (hgenerators : ∀ j, generators j ∈ binaryCSSCheckSet xCode zCode)
    {P : Binary ι} (hP : GeneratedStabilizer generators P) :
    P.phase = 0 ∧ P.vector.xPart ∈ xCode.carrier ∧
      P.vector.zPart ∈ zCode.carrier := by sorry
