-- Prove2me | Theorems.Thm_QEC_Coding_ChainComplexData_firstCoboundaryCheckCode_orthogonal_middleBoundaryCode
-- name    : QEC.Coding.ChainComplexData.firstCoboundaryCheckCode_orthogonal_middleBoundaryCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:33:33.482193+00:00
-- url     : https://prove2.me/theorems/06965f2c-9adb-43a3-87c4-271f352aae52
-- title:
--   Chain Complex Data: first Coboundary Check Code orthogonal middle Boundary Code
-- statement:
--   The coboundary X-check code is symplectically orthogonal to the middle-boundary
--   Z-check code induced by the same chain-complex boundary maps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L785-L794
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L785-L794

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.ChainComplexData
variable {F : Type u} {ι : Type v} {C0 C2 : Type (max u v)} [Field F] [Fintype F]
    [Fintype ι] [AddCommGroup C0] [Module F C0] [AddCommGroup C2] [Module F C2]

theorem QEC.Coding.ChainComplexData.firstCoboundaryCheckCode_orthogonal_middleBoundaryCode {κ : Type v} [Fintype κ]
    (K : ChainComplexData F (Word F κ) (Word F ι) C2) :
    ∀ x : Word F ι, x ∈ K.firstCoboundaryCheckCode.carrier →
      ∀ z : Word F ι, z ∈ K.middleBoundaryCode.carrier →
        symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector F ι)
          ({ xPart := 0, zPart := z } : SymplecticVector F ι) = 0 := by sorry
