-- Prove2me | Theorems.Thm_ThresholdTheorem_zero_level_block_simulation
-- name    : ThresholdTheorem.zero_level_block_simulation
-- status  : Proved
-- author  : @Imine
-- created : 2026-10-21T12:53:22.492346+00:00
-- url     : https://prove2.me/theorems/331cbbba-3a15-487e-a3f4-a9906028bbef
-- title:
--   Level-zero quantum circuit simulation by one-qubit blocks
-- statement:
--   In the unencoded (level-zero) case of the layered quantum-circuit noise model, relabel each logical qubit as a one-qubit physical block and decode each block by reading its sole bit. For every constant $c\ge 1$, every circuit $C$ and every physical fault rate $p\ge 0$ satisfying $cp<1$, one can choose a relabeled circuit $C^\prime$ of exactly the same number of locations so that every permitted independent stochastic noise model obeys
--
--   $$
--   \operatorname{TV}(\operatorname{decode}(\operatorname{out}(C^\prime_{\mathrm{noisy}})),\operatorname{out}(C_{\mathrm{ideal}}))\le p\,|C|.
--   $$
--
--   This is the base case for concatenated fault-tolerant simulation. Its construction is uniform in the noise model and preserves the circuit's operation order, locations and size.
-- source:
--   Exact k=0 base case of Prove2Me ThresholdTheorem.level_k_concatenated_simulation, theorem 6d175c37-2a54-43c5-89c0-14cf15f2cfd5, https://prove2.me/theorems/6d175c37-2a54-43c5-89c0-14cf15f2cfd5 ; underlying stochastic-fault model is Definitions.Def_threshold_theorem_noise_model.

import Mathlib
import Definitions.Def_threshold_theorem_noise_model

open ThresholdTheorem

namespace ThresholdTheorem
theorem zero_level_block_simulation :
    ∀ c : ℝ, 1 ≤ c →
      ∃ (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2),
        ∀ (n : ℕ) (C : Circuit (Fin n)),
          ∃ C' : Circuit (Fin n × Fin b),
            (C'.size : ℝ) ≤ C.size ∧
            ∀ (p : ℝ), 0 ≤ p → c * p < 1 → ∀ N : NoiseModel p,
              tvDist (decodeDist dec (outDist (noisyState N C')))
                (outDist (idealState C)) ≤ p * C.size := by sorry
end ThresholdTheorem
