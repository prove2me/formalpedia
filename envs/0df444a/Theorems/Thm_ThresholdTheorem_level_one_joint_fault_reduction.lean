-- Prove2me | Theorems.Thm_ThresholdTheorem_level_one_joint_fault_reduction
-- name    : ThresholdTheorem.level_one_joint_fault_reduction
-- status  : Open
-- author  : @shivm
-- created : 2026-10-25T21:22:13.587283+00:00
-- url     : https://prove2.me/theorems/6c64441d-3447-4fb2-a8e5-3b820457fd00
-- title:
--   Level reduction: decoded level-1 runs are runs of $C$ with joint faults on the bad exRecs of each layer
-- statement:
--   **Level reduction with joint faults on the decoded side (Aliferis–Gottesman–Preskill).** There are constants $M\in\mathbb N$ and $A$, a block size $b$ and a block decoder $\mathrm{dec}:\{0,1\}^b\to\{0,1\}$ with the following property. Let $C$ be any layered circuit on a finite set of qubits $Q$, built from the gates $H,T,\mathrm{CNOT}$, preparations of $|0\rangle$ and waits, with no intermediate measurements. Then $C$ has a level-one simulation $C'$ on $Q\times\{0,\dots,b-1\}$ (block $q$ encodes qubit $q$, ancillas included) with $|C'|\le A\,|C|$. It comes with a family $\mathrm{pairs}(\ell)$ of at most $M$ two-element sets of locations of $C'$ for each location $\ell$ of $C$, and a map $\Psi$ from sets $F$ of faulty locations of $C'$ to sets of locations of $C$ (the bad extended rectangles). These satisfy:
--
--   1. **(disjoint witnesses, including predecessors)** For every $F$ and every $S\subseteq\Psi(F)\cup\mathrm{pred}_C(\Psi(F))$ one can pick, for each $\ell\in S$, a pair $g(\ell)\in\mathrm{pairs}(\ell)$ with $g(\ell)\subseteq F$, such that the pairs $g(\ell)$, $\ell\in S$, are pairwise disjoint.
--   2. **(exact representation with joint faults)** For every environment size $m$ there is $m'$ with the following property. Take any fault set $F$ and any fault channels on $C'$, each acting on its location's qubits and an $m$-qubit environment, with the faulty locations acting one after another as in `faultyState`. Then there are joint faults $J_t$ on $C$, with data qubits in $\mathrm{bad}_t(\Psi(F))$ and an $m'$-qubit environment, such that
--   $$(\mathrm{blockMap}\,\mathrm{dec})_*\,P\big(C',F,\mathrm{fault}\big)\;=\;P_{\mathrm{joint}}\big(C,\Psi(F),(J_t)_t\big).$$
--
--   **Intended construction.** Encode each qubit in a code concatenated enough times that every gadget is fault tolerant to order $t_0$: an extended rectangle (exRec) with at most $t_0$ faults is exactly correct. The gadgets are measurement-free, with coherent syndrome processing on fresh $|0\rangle$ ancillas as in Aharonov–Ben-Or. Concatenating a distance-3 scheme $r$ times gives $t_0=2^r-1$. Let $\Psi(F)$ be the set of locations whose exRec contains more than $t_0$ faults. The ideal decoder is inserted after the error correction that ends every layer of the simulation, at the same time for all blocks. Then good exRecs decode to ideal gates. The bad exRecs that simulate one layer of $C$, together with the syndrome registers and the environment, decode to one joint fault on that layer. For $t_0$ large (for example $t_0\ge 26$), every bad exRec contains enough faults to supply disjoint witness pairs both for itself and for its at most two predecessors.
--
--   **Role.** Together with `jointFaultyState_sequentialize` this gives `level_one_fault_set_reduction`. The decoded faults of one layer are first represented as a joint fault, and then turned into sequential faults on $\Psi(F)\cup\mathrm{pred}_C(\Psi(F))$.
-- source:
--   P. Aliferis, D. Gottesman, J. Preskill, Quantum accuracy threshold for concatenated distance-3 codes, Quantum Inf. Comput. 6 (2006) 97-165, arXiv:quant-ph/0504218, Sec. 3 (exRecs; good exRecs are correct), Sec. 5 (level reduction under local stochastic noise); D. Gottesman, arXiv:0904.2557, Sec. 5; D. Aharonov, M. Ben-Or, Fault-tolerant quantum computation with constant error rate, SIAM J. Comput. 38 (2008), arXiv:quant-ph/9906129 (measurement-free fault tolerance with fresh qubits).

import Mathlib
import Definitions.Def_threshold_theorem_joint_faults

open ThresholdTheorem

namespace ThresholdTheorem
theorem level_one_joint_fault_reduction :
    ∃ (M : ℕ) (A : ℝ) (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2),
      ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (C : Circuit Q),
        ∃ C' : Circuit (Q × Fin b), (C'.size : ℝ) ≤ A * C.size ∧
          ∃ (pairs : ℕ × ℕ → Finset (Finset (ℕ × ℕ)))
            (Ψ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ)),
            (∀ ℓ, (pairs ℓ).card ≤ M) ∧ (∀ ℓ, ∀ p ∈ pairs ℓ, p.card = 2) ∧
            (∀ (F S : Finset (ℕ × ℕ)), S ⊆ Ψ F ∪ predLocs C (Ψ F) →
              ∃ g : ℕ × ℕ → Finset (ℕ × ℕ), (∀ ℓ ∈ S, g ℓ ∈ pairs ℓ ∧ g ℓ ⊆ F) ∧
                ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ → Disjoint (g ℓ₁) (g ℓ₂)) ∧
            ∀ m : ℕ, ∃ m' : ℕ, ∀ (F : Finset (ℕ × ℕ))
              (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m)),
              ∃ J : ℕ → JointFault Q m',
                (∀ t i, (J t).supp i ∈ badQubits C (Ψ F) t) ∧
                pushDist (blockMap dec) (dataOutDist (faultyState F fault C')) =
                  dataOutDist (jointFaultyState (Ψ F) J C) := by sorry
end ThresholdTheorem
