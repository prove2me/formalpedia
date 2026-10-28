-- Prove2me | Theorems.Thm_ThresholdTheorem_level_one_sparse_fault_correctness
-- name    : ThresholdTheorem.level_one_sparse_fault_correctness
-- status  : Open
-- author  : @shivm
-- created : 2026-10-25T20:19:55.022269+00:00
-- url     : https://prove2.me/theorems/9d54e052-2c5b-4fd4-9eed-405fc55cacd0
-- title:
--   Level-one encoded simulation is exactly correct when no malignant pair of locations fails
-- statement:
--   **Level-one fault tolerance against sparse faults (good extended rectangles are correct).** There are constants $M$ and $A$, a block size $b$ and a classical decoder $\mathrm{dec}:\{0,1\}^b\to\{0,1\}$ with the following property. Every ideal circuit $C$ on $n$ qubits has an encoded simulation $C'$ on $n$ blocks of $b$ physical qubits with $|C'|\le A\,|C|$, together with a set $B$ of *malignant pairs* of locations of $C'$ (a location being a pair $(t,j)$: location number $j$ of layer number $t$), with
--   $$|B|\le M\,|C|$$
--   and each pair consisting of two **distinct** locations, such that the simulation is **exactly correct whenever the set of faulty locations contains no malignant pair**: for every deterministic fault pattern — a noise model in which each location is faulty with probability $0$ or $1$ and each faulty location applies an arbitrary quantum channel — in which no pair in $B$ has both locations faulty, the blockwise-decoded measurement distribution of $C'$ equals the ideal output distribution of $C$:
--   $$\mathrm{dec}_*P_{\text{faulty}}(C') = P_{\mathrm{ideal}}(C).$$
--
--   This is the combinatorial core of the level-one threshold argument: one encodes each logical qubit in a distance-3 quantum code (with its ancillas inside the block), replaces each location of $C$ by a fault-tolerant gadget followed by (coherent, measurement-free) error correction, and takes $B$ to be the set of pairs of distinct locations lying in a common extended rectangle. Since each extended rectangle has boundedly many locations and there is one per location of $C$, $|B|=O(|C|)$; and the standard lemma says that if every extended rectangle contains at most one fault then the simulation, followed by ideal decoding, reproduces the ideal computation exactly (for arbitrary fault channels, by linearity). In the formalization a deterministic fault pattern is a `NoiseModel 1` whose probabilities are all $0$ or $1$; a location with probability $1$ applies its fault channel instead of its ideal operation.
-- source:
--   P. Aliferis, D. Gottesman, J. Preskill, Quantum accuracy threshold for concatenated distance-3 codes, Quantum Inf. Comput. 6 (2006) 97-165, arXiv:quant-ph/0504218, Sec. 3 (extended rectangles; Lemma 2: good exRecs are correct) and Sec. 5 (level-1 counting of malignant pairs); D. Aharonov, M. Ben-Or, Fault-tolerant quantum computation with constant error rate, SIAM J. Comput. 38 (2008), arXiv:quant-ph/9906129 (measurement-free fault tolerance with fresh qubits); context: Nielsen & Chuang, Quantum Computation and Quantum Information, 10th anniv. ed., Sec. 10.6.1, pp. 480-481.

import Mathlib
import Definitions.Def_threshold_theorem_noise_model

open ThresholdTheorem

namespace ThresholdTheorem
theorem level_one_sparse_fault_correctness :
    ∃ (M A : ℝ) (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2),
      ∀ (n : ℕ) (C : Circuit (Fin n)), ∃ C' : Circuit (Fin n × Fin b),
        (C'.size : ℝ) ≤ A * C.size ∧
        ∃ B : Finset ((ℕ × ℕ) × (ℕ × ℕ)), (B.card : ℝ) ≤ M * C.size ∧
          (∀ x ∈ B, x.1 ≠ x.2) ∧
          ∀ N : NoiseModel 1, (∀ t j, N.prob t j = 0 ∨ N.prob t j = 1) →
            (∀ x ∈ B, N.prob x.1.1 x.1.2 = 0 ∨ N.prob x.2.1 x.2.2 = 0) →
            decodeDist dec (outDist (noisyState N C')) = outDist (idealState C) := by sorry
end ThresholdTheorem
