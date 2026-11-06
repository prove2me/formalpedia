-- Prove2me | Theorems.Thm_QEC_Coding_symplecticForm_x_zero_zero_z_eq_wordPairing
-- name    : QEC.Coding.symplecticForm_x_zero_zero_z_eq_wordPairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:15:05.070343+00:00
-- url     : https://prove2.me/theorems/36fe1a45-d991-4919-a935-c4b6cef2417a
-- title:
--   Coding: symplectic Form x zero zero z eq word Pairing
-- statement:
--   The CSS X/Z symplectic pairing reduces to the finite-coordinate word pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L528-L533
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L528-L533

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x

theorem QEC.Coding.symplecticForm_x_zero_zero_z_eq_wordPairing {F : Type u} {ι : Type v}
    [Field F] [Fintype F] [Fintype ι] (x z : Word F ι) :
    symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector F ι)
        ({ xPart := 0, zPart := z } : SymplecticVector F ι) =
      wordPairing (F := F) (ι := ι) x z := by sorry
