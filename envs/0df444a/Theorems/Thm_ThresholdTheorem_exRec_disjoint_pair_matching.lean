-- Prove2me | Theorems.Thm_ThresholdTheorem_exRec_disjoint_pair_matching
-- name    : ThresholdTheorem.exRec_disjoint_pair_matching
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T20:14:02.741198+00:00
-- url     : https://prove2.me/theorems/4457b03c-9101-4fbc-abdd-4212da7ede1b
-- title:
--   Disjoint fault-pair matching for extended rectangles and their predecessors
-- statement:
--   This theorem establishes the combinatorial disjoint witness-pair property for extended rectangles (exRecs) and their predecessor locations in a layered quantum circuit.
--
--   Let $C$ be a layered circuit over $\{H, T, \mathrm{CNOT}, \mathrm{prep}, \mathrm{wait}\}$ on a qubit set $Q$, and let $\mathrm{exRec}(\ell)$ assign to each location $\ell$ of $C$ a finite set of physical locations of size at most $R_{\max}$ such that two extended rectangles $\mathrm{exRec}(\ell_1)$ and $\mathrm{exRec}(\ell_2)$ can overlap only when $\ell_1 = \ell_2$, $\ell_1 \in \mathrm{pred}_C(\{\ell_2\})$, or $\ell_2 \in \mathrm{pred}_C(\{\ell_1\})$. Suppose that for every fault set $F$, every bad location $\ell \in \Psi(F)$ contains at least $30$ faults in $\mathrm{exRec}(\ell) \cap F$.
--
--   Then there exists a family $\mathrm{pairs}(\ell)$ of two-element sets of physical locations with
--
--   $$
--   |\mathrm{pairs}(\ell)| \le \binom{3 R_{\max}}{2}
--   $$
--
--   such that for every fault set $F$ and every subset $S \subseteq \Psi(F) \cup \mathrm{pred}_C(\Psi(F))$, one can assign to each $\ell \in S$ a pair $g(\ell) \in \mathrm{pairs}(\ell)$ with $g(\ell) \subseteq F$ so that the pairs $\{g(\ell)\}_{\ell \in S}$ are pairwise disjoint.
--
--   Because each operation in $C$ has arity at most $2$ and each layer partitions $Q$, every location has at most $2$ predecessors and at most $2$ successors, allowing each bad exRec to supply disjoint fault pairs both for itself and for its predecessors even in the presence of overlapping adjacent exRecs.
--
--   **Formalization Note** Predecessor locations are given by `predLocs C`, and the binomial bound is written `(3 * R_max).choose 2`.
-- source:
--   P. Aliferis, D. Gottesman, J. Preskill, Quantum accuracy threshold for concatenated distance-3 codes, Quantum Inf. Comput. 6 (2006) 97-165, arXiv:quant-ph/0504218, Sec. 3 and Sec. 5; D. Gottesman, arXiv:0904.2557, Sec. 5.

import Mathlib
import Definitions.Def_threshold_theorem_joint_faults

open ThresholdTheorem

namespace ThresholdTheorem
theorem exRec_disjoint_pair_matching {Q : Type} [DecidableEq Q]
    (R_max : ℕ) (C : Circuit Q)
    (exRec : ℕ × ℕ → Finset (ℕ × ℕ))
    (Ψ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ))
    (h_card : ∀ ℓ, (exRec ℓ).card ≤ R_max)
    (h_overlap : ∀ ℓ₁ ℓ₂, (exRec ℓ₁ ∩ exRec ℓ₂).Nonempty →
      ℓ₁ = ℓ₂ ∨ ℓ₁ ∈ predLocs C {ℓ₂} ∨ ℓ₂ ∈ predLocs C {ℓ₁})
    (h_bad : ∀ F ℓ, ℓ ∈ Ψ F → 30 ≤ (exRec ℓ ∩ F).card) :
    ∃ pairs : ℕ × ℕ → Finset (Finset (ℕ × ℕ)),
      (∀ ℓ, (pairs ℓ).card ≤ (3 * R_max).choose 2) ∧
      (∀ ℓ, ∀ p ∈ pairs ℓ, p.card = 2) ∧
      ∀ (F S : Finset (ℕ × ℕ)), S ⊆ Ψ F ∪ predLocs C (Ψ F) →
        ∃ g : ℕ × ℕ → Finset (ℕ × ℕ),
          (∀ ℓ ∈ S, g ℓ ∈ pairs ℓ ∧ g ℓ ⊆ F) ∧
          ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ → Disjoint (g ℓ₁) (g ℓ₂) := by sorry
end ThresholdTheorem
