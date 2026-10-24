-- Prove2me | Theorems.Thm_ThresholdTheorem_tvDist_decodeDist_le
-- name    : ThresholdTheorem.tvDist_decodeDist_le
-- status  : Proved
-- author  : @Imine
-- created : 2026-10-21T12:54:54.910273+00:00
-- url     : https://prove2.me/theorems/be9089ee-66bc-406e-921a-98c746feb428
-- title:
--   Block decoding contracts finite total-variation distance
-- statement:
--   Let $P$ and $Q$ be arbitrary real-valued functions on the finite set of physical measurement strings of $n$ blocks of $b$ bits. Decode each block deterministically into one logical bit and push both functions forward by summing over the fibers of this decoding map. Then
--
--   $$
--   \operatorname{TV}(\operatorname{decode}_*P,\operatorname{decode}_*Q)\le\operatorname{TV}(P,Q).
--   $$
--
--   This finite data-processing inequality requires no positivity or normalization assumptions on $P$ and $Q$. It allows a physical output error bound to pass unchanged through the block decoder in the threshold-theorem circuit model.
-- source:
--   Finite-fiber triangle inequality for the decodeDist and tvDist definitions in Prove2Me Definitions.Def_threshold_theorem_noise_model, used by ThresholdTheorem.level_k_concatenated_simulation (theorem 6d175c37-2a54-43c5-89c0-14cf15f2cfd5, https://prove2.me/theorems/6d175c37-2a54-43c5-89c0-14cf15f2cfd5).

import Definitions.Def_threshold_theorem_noise_model

open ThresholdTheorem

namespace ThresholdTheorem
theorem tvDist_decodeDist_le {n b : ℕ}
    (dec : (Fin b → Fin 2) → Fin 2)
    (P Q : (Fin n × Fin b → Fin 2) → ℝ) :
    tvDist (decodeDist dec P) (decodeDist dec Q) ≤ tvDist P Q := by sorry
end ThresholdTheorem
