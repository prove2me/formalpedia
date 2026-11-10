-- Prove2me | Theorems.Thm_Pr6453Tensor_checkBasis_sound
-- name    : Pr6453Tensor.checkBasis_sound
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-09T08:53:50.038693+00:00
-- url     : https://prove2.me/theorems/160c405b-61f3-4830-8497-726eb95060eb
-- title:
--   PR #6453: soundness of the basis-tensor checker
-- statement:
--   Soundness of the basis-tensor checker: if the checker passes on every basis tensor then the composite read∘M∘enc agrees with the required form P at each basis tensor e_i ⊗ e_j. Combined with the reduction of the incidence, this turns the specification of a word into 1152 x 1152 evaluations on basis tensors.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, RESULT.json (module block).

import Definitions.Def_Pr6453_TensorEnc
import Mathlib

set_option autoImplicit false

namespace Pr6453Tensor

theorem checkBasis_sound {m n c : ℕ} (row : Fin m → Fin n → (Fin c → ℚ))
    (M : (Fin c → ℚ) →ₗ[ℚ] (Fin c → ℚ)) (read : (Fin c → ℚ) →ₗ[ℚ] (Fin c → ℚ))
    (P : Fin m → Fin n → (Fin c → ℚ))
    (h : checkBasis row M read P = true) (i : Fin m) (j : Fin n) :
    read (M (enc row (Pi.single i 1 ⊗ₜ[ℚ] Pi.single j 1))) = P i j := by
  sorry

end Pr6453Tensor
