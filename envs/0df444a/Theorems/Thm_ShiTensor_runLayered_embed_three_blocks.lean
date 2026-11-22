-- Prove2me | Theorems.Thm_ShiTensor_runLayered_embed_three_blocks
-- name    : ShiTensor.runLayered_embed_three_blocks
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T04:45:35.130248+00:00
-- url     : https://prove2.me/theorems/791cc4cb-5a72-4f94-8b7d-18075c7813c6
-- title:
--   Three circuits on disjoint wire blocks act on the three tensor factors independently
-- statement:
--   Relabel three circuits onto the three blocks of a register whose wire count is split with the sum associated to the left, concatenate them, and run the result on a product of three states. The outcome is the product of the three states each evolved by its own circuit: no block disturbs another.
--
--   This is what licenses analysing repeated copies of a verifier independently while they share one register, and it is obtained by peeling each two-step block inclusion into its two single-step parts and applying the corresponding one-block laws.

import Definitions.Def_ShiTensor_Core
import Definitions.Def_ShiEmbed_Core

set_option autoImplicit false

namespace ShiTensor

open ShiShallow

theorem runLayered_embed_three_blocks {m p q : ℕ} (c1 : Layered m) (c2 : Layered p) (c3 : Layered q)
    (ψ1 : QState m) (ψ2 : QState p) (ψ3 : QState q) :
    runLayered
        (ShiEmbed.embedCirc
            ((Fin.castAdd q : Fin (m + p) → Fin (m + p + q)) ∘
              (Fin.castAdd p : Fin m → Fin (m + p)))
            ((Fin.castAdd_injective (m + p) q).comp (Fin.castAdd_injective m p)) c1
          ++ ShiEmbed.embedCirc
            ((Fin.castAdd q : Fin (m + p) → Fin (m + p + q)) ∘
              (Fin.natAdd m : Fin p → Fin (m + p)))
            ((Fin.castAdd_injective (m + p) q).comp (Fin.natAdd_injective p m)) c2
          ++ ShiEmbed.embedCirc (Fin.natAdd (m + p) : Fin q → Fin (m + p + q))
            (Fin.natAdd_injective q (m + p)) c3)
        (tensor (tensor ψ1 ψ2) ψ3)
      = tensor (tensor (runLayered c1 ψ1) (runLayered c2 ψ2)) (runLayered c3 ψ3) := by
  sorry

end ShiTensor
