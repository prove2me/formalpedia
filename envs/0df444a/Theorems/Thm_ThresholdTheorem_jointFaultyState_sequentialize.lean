-- Prove2me | Theorems.Thm_ThresholdTheorem_jointFaultyState_sequentialize
-- name    : ThresholdTheorem.jointFaultyState_sequentialize
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-25T21:22:17.730041+00:00
-- url     : https://prove2.me/theorems/9bdbfbfe-ffa0-4840-9559-86b65520ba4c
-- title:
--   Joint layer faults become sequential faults once predecessor locations are faulty too
-- statement:
--   **Joint layer faults can be sequentialized at the cost of the predecessor locations.** Let $C$ be a layered circuit on a finite set of qubits $Q$ and let $m\in\mathbb N$. Then there is $m'\in\mathbb N$ with the following property. Let $B$ be any set of locations of $C$. For each layer $t$ let $J_t$ be a joint fault, i.e. a channel acting jointly on some data qubits and the $m$-qubit environment, whose data qubits lie in $\mathrm{bad}_t(B)$, the set of qubits of the locations $(t,j)\in B$. Then there are fault channels $\mathrm{fault}'$, each acting on the qubits of its location together with an $m'$-qubit environment, such that the measured data distributions agree:
--   $$P_{\mathrm{joint}}\big(C,B,(J_t)_t\big)\;=\;P\big(C,\;B\cup\mathrm{pred}_C(B),\;\mathrm{fault}'\big).$$
--   Here the left side is the joint-fault execution `jointFaultyState` with the environment traced out. The right side is the ordinary faulty execution `faultyState` with the environment traced out. In the ordinary execution the faulty locations of a layer act one after another, in their order in the layer, and $\mathrm{pred}_C(B)$ is the set of locations of the previous layer that share a qubit with a location of $B$.
--
--   **Role.** In the level reduction one decodes a faulty level-one simulation. The bad extended rectangles that simulate the locations of one layer of $C$ run concurrently, and their faults can exchange information through the environment in both directions. In the decoded picture they therefore act as one joint fault on that layer. The sequential fault model of `faultyState` cannot express such a two-way interaction among the faulty locations of a single layer. This lemma removes the mismatch: if the predecessors of the bad locations are also declared faulty, every joint fault becomes an ordinary sequential one.
--
--   **Formalization note.** $m'$ may depend on $C$ and $m$ but not on $B$ or $J$.
-- source:
--   Auxiliary lemma for the level reduction of P. Aliferis, D. Gottesman, J. Preskill, arXiv:quant-ph/0504218, Sec. 5. It converts the joint fault model of Prove2Me definition threshold_theorem_joint_faults into the sequential fault model of threshold_theorem_local_stochastic (faultyState).

import Mathlib
import Definitions.Def_threshold_theorem_joint_faults

open ThresholdTheorem

namespace ThresholdTheorem
theorem jointFaultyState_sequentialize {Q : Type} [Fintype Q] [DecidableEq Q]
    (C : Circuit Q) (m : ℕ) :
    ∃ m' : ℕ, ∀ (B : Finset (ℕ × ℕ)) (J : ℕ → JointFault Q m),
      (∀ t i, (J t).supp i ∈ badQubits C B t) →
      ∃ fault' : ℕ → ℕ → (k : ℕ) → Channel (k + m'),
        dataOutDist (jointFaultyState B J C) =
          dataOutDist (faultyState (B ∪ predLocs C B) fault' C) := by sorry
end ThresholdTheorem
