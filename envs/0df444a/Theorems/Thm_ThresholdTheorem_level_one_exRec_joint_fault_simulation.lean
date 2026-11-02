-- Prove2me | Theorems.Thm_ThresholdTheorem_level_one_exRec_joint_fault_simulation
-- name    : ThresholdTheorem.level_one_exRec_joint_fault_simulation
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-01T20:14:10.46442+00:00
-- url     : https://prove2.me/theorems/801b4afd-4e9e-4717-a0c6-45afcceb1d87
-- title:
--   Level-1 extended-rectangle simulation with joint faults on bad exRecs
-- statement:
--   This theorem states the quantum extended-rectangle (exRec) simulation property for level-one fault-tolerant encoding with high-order error correction.
--
--   There exist constants $R_{\max} \in \mathbb{N}$ and $A \in \mathbb{R}$, a block size $b \in \mathbb{N}$, and a classical block decoder $\mathrm{dec} : \{0,1\}^b \to \{0,1\}$ such that every layered circuit $C$ on a finite qubit set $Q$ admits a level-one encoded circuit $C'$ on $Q \times \{0, \dots, b-1\}$ with $|C'| \le A |C|$, an extended-rectangle assignment $\mathrm{exRec}(\ell)$ of size at most $R_{\max}$ overlapping only between a location and its predecessors/successors, and a bad-location map $\Psi(F)$ consisting of locations with at least $30$ faults in $\mathrm{exRec}(\ell) \cap F$, such that for every environment size $m$ there is an environment size $m'$ where for any fault set $F$ and fault channels $\mathrm{fault}$ on $C'$, there exist layer-wise joint faults $J_t$ supported on $\mathrm{bad}_t(\Psi(F))$ satisfying
--
--   $$
--   (\mathrm{blockMap}\,\mathrm{dec})_* P(C', F, \mathrm{fault}) = P_{\mathrm{joint}}(C, \Psi(F), (J_t)_t).
--   $$
--
--   This isolates the quantum gadget and ideal-decoder commutation argument of Aliferis–Gottesman–Preskill from the combinatorial matching of disjoint fault pairs across extended rectangles and their predecessors.
--
--   **Formalization Note** Combined with `ThresholdTheorem.exRec_disjoint_pair_matching`, this directly yields `ThresholdTheorem.level_one_joint_fault_reduction` with $M = \binom{3 R_{\max}}{2}$.
-- source:
--   P. Aliferis, D. Gottesman, J. Preskill, Quantum accuracy threshold for concatenated distance-3 codes, Quantum Inf. Comput. 6 (2006) 97-165, arXiv:quant-ph/0504218, Sec. 3 and Sec. 5; D. Aharonov, M. Ben-Or, SIAM J. Comput. 38 (2008), arXiv:quant-ph/9906129.

import Mathlib
import Definitions.Def_threshold_theorem_joint_faults

open ThresholdTheorem

namespace ThresholdTheorem
theorem level_one_exRec_joint_fault_simulation :
    ∃ (R_max : ℕ) (A : ℝ) (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2),
      ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (C : Circuit Q),
        ∃ C' : Circuit (Q × Fin b), (C'.size : ℝ) ≤ A * C.size ∧
          ∃ (exRec : ℕ × ℕ → Finset (ℕ × ℕ))
            (Ψ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ)),
            (∀ ℓ, (exRec ℓ).card ≤ R_max) ∧
            (∀ ℓ₁ ℓ₂, (exRec ℓ₁ ∩ exRec ℓ₂).Nonempty →
              ℓ₁ = ℓ₂ ∨ ℓ₁ ∈ predLocs C {ℓ₂} ∨ ℓ₂ ∈ predLocs C {ℓ₁}) ∧
            (∀ F ℓ, ℓ ∈ Ψ F → 30 ≤ (exRec ℓ ∩ F).card) ∧
            ∀ m : ℕ, ∃ m' : ℕ, ∀ (F : Finset (ℕ × ℕ))
              (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m)),
              ∃ J : ℕ → JointFault Q m',
                (∀ t i, (J t).supp i ∈ badQubits C (Ψ F) t) ∧
                pushDist (blockMap dec) (dataOutDist (faultyState F fault C')) =
                  dataOutDist (jointFaultyState (Ψ F) J C) := by sorry
end ThresholdTheorem
