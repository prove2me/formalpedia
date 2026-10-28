-- Prove2me | Theorems.Thm_ThresholdTheorem_level_one_fault_set_reduction
-- name    : ThresholdTheorem.level_one_fault_set_reduction
-- status  : Open
-- author  : @shivm
-- created : 2026-10-25T20:45:45.4284+00:00
-- url     : https://prove2.me/theorems/7d5573fd-dbc8-4ef2-af60-7308d3d71abb
-- title:
--   Level reduction for a fixed fault set: decoded level-1 runs are runs of $C$ faulty on bad exRecs
-- statement:
--   **Level reduction for a fixed fault set (Aliferis–Gottesman–Preskill).** There are a constant $M\in\mathbb N$, a constant $A$, a block size $b$ and a block decoder $\mathrm{dec}:\{0,1\}^b\to\{0,1\}$ with the following property. Every layered circuit $C$ on a finite set of qubits $Q$ (gates $H,T,\mathrm{CNOT}$, preparations of $|0\rangle$ and waits; no intermediate measurements) has a level-one simulation $C'$ on $Q\times\{0,\dots,b-1\}$ (block $q$ encodes qubit $q$, ancillas included in the block) with $|C'|\le A\,|C|$, together with
--
--   * for each location $\ell=(t,j)$ of $C$, a family $\mathrm{pairs}(\ell)$ of at most $M$ two-element sets of locations of $C'$ (in the intended construction: all pairs of locations inside the extended rectangle $\mathrm{exRec}(\ell)$ simulating $\ell$), and
--   * a map $\Phi$ sending a set $F$ of faulty locations of $C'$ to a set $\Phi(F)$ of locations of $C$ (the *bad* extended rectangles),
--
--   such that:
--
--   1. **(disjoint witnesses)** for every $F$ and every $S\subseteq\Phi(F)$ one can choose, for each $\ell\in S$, a pair $g(\ell)\in\mathrm{pairs}(\ell)$ with $g(\ell)\subseteq F$, the pairs $g(\ell)$, $\ell\in S$, being pairwise disjoint;
--   2. **(exact representation)** for every environment size $m$ there is $m'$ such that for every fault set $F$ and every choice of fault channels on $C'$ (acting jointly on the location's qubits and an $m$-qubit environment), there are fault channels on $C$ (with an $m'$-qubit environment) for which the blockwise-decoded measured output distribution of the faulty run of $C'$ equals exactly the measured output distribution of the run of $C$ in which precisely the locations of $\Phi(F)$ are faulty:
--   $$(\mathrm{blockMap}\,\mathrm{dec})_*\,P\big(C',F,\text{fault}\big)=P\big(C,\Phi(F),\text{fault}'\big).$$
--
--   This is the deterministic (fault-pattern-wise) content of the level reduction. One encodes each qubit in a distance-3 CSS code, replaces each location by a fault-tolerant, measurement-free gadget (coherent syndrome processing with fresh $|0\rangle$ ancillas, as in Aharonov–Ben-Or) followed by error correction, and lets $\mathrm{exRec}(\ell)$ consist of the gadget with its leading and trailing error corrections. $\Phi(F)$ is the set of bad exRecs, determined backwards in time with AGP truncation: a trailing EC belonging to a later bad exRec is removed from the earlier exRec before counting. An exRec is bad if its (truncated) part contains two faults of $F$. With this rule each fault is charged to at most one bad exRec, which is property 1. Property 2 is the AGP argument that good (truncated) exRecs are correct. One inserts an ideal decoder (an isomorphism block $\cong$ logical qubit $\otimes$ syndrome) at the end and moves it backwards through the circuit. Good exRecs become ideal logical locations; bad ones become arbitrary channels on the logical qubits, the syndrome registers and the environment. The syndrome registers become part of the new environment, so $m'=m+|Q|(b-1)$ suffices.
-- source:
--   P. Aliferis, D. Gottesman, J. Preskill, Quantum accuracy threshold for concatenated distance-3 codes, Quantum Inf. Comput. 6 (2006) 97-165, arXiv:quant-ph/0504218, Sec. 3 (exRecs, Lemma 'good exRecs are correct'), Sec. 5 (level reduction, truncation of overlapping bad exRecs, local stochastic noise); D. Gottesman, An introduction to quantum error correction and fault-tolerant quantum computation, arXiv:0904.2557, Sec. 5 (level reduction); D. Aharonov, M. Ben-Or, Fault-tolerant quantum computation with constant error rate, SIAM J. Comput. 38 (2008), arXiv:quant-ph/9906129 (measurement-free fault tolerance with fresh qubits).

import Mathlib
import Definitions.Def_threshold_theorem_local_stochastic

open ThresholdTheorem

namespace ThresholdTheorem
theorem level_one_fault_set_reduction :
    ∃ (M : ℕ) (A : ℝ) (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2),
      ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (C : Circuit Q),
        ∃ C' : Circuit (Q × Fin b), (C'.size : ℝ) ≤ A * C.size ∧
          ∃ (pairs : ℕ × ℕ → Finset (Finset (ℕ × ℕ)))
            (Φ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ)),
            (∀ ℓ, (pairs ℓ).card ≤ M) ∧ (∀ ℓ, ∀ p ∈ pairs ℓ, p.card = 2) ∧
            (∀ (F S : Finset (ℕ × ℕ)), S ⊆ Φ F →
              ∃ g : ℕ × ℕ → Finset (ℕ × ℕ), (∀ ℓ ∈ S, g ℓ ∈ pairs ℓ ∧ g ℓ ⊆ F) ∧
                ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ → Disjoint (g ℓ₁) (g ℓ₂)) ∧
            ∀ m : ℕ, ∃ m' : ℕ, ∀ (F : Finset (ℕ × ℕ))
              (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m)),
              ∃ fault' : ℕ → ℕ → (k : ℕ) → Channel (k + m'),
                pushDist (blockMap dec) (dataOutDist (faultyState F fault C')) =
                  dataOutDist (faultyState (Φ F) fault' C) := by sorry
end ThresholdTheorem
