-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P04_perfectAdaptiveErasure
-- name    : QAlgorithms.Papers.Independent.Gap48.P04.perfectAdaptiveErasure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:59:16.768376+00:00
-- url     : https://prove2.me/theorems/af58f313-6ac6-4e68-8256-9ae6500b9b5e
-- title:
--   Perfect adaptive quantum transmission for every erasure pattern
-- statement:
--   Let $n\ge1$ and let $t$ be an integer with $0\le t\le n$. There exists one finite adaptive protocol $P$, with exactly $n$ forward qubit-channel slots, free two-way classical communication, arbitrary finite local quantum memory, and no initially shared entanglement, which transmits $n-t$ unknown qubits perfectly for every set $S\subseteq\{0,\ldots,n-1\}$ of $t$ erased slots. The protocol is chosen before $S$ and the normalized unknown input $|\psi\rangle$. Each slot is evaluated as an identity transmission with an intact flag outside $S$, or a complete flagged erasure in $S$. Its output $\rho_{P,S,\psi}$ satisfies
--
--   $$\forall S\ (|S|=t),\ \forall\psi\ (\|\psi\|=1),\qquad \langle\psi|\rho_{P,S,\psi}|\psi\rangle=1,\qquad \frac{n-t}{n}=1-\frac tn.$$
--
--   The schedule is accessed only through the channel slots, so erased locations are learned from the output and feedback. At $t=n$ the logical register is the one-dimensional zero-qubit space. This is an exact finite-block worst-pattern guarantee, separate from stochastic asymptotic capacity.
-- source:
--   Capacities of Quantum Erasure Channels, arXiv:quant-ph/9701015v2, PDF p. 4, Unnumbered teleportation guarantee

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P04

namespace QAlgorithms.Papers.Independent.Gap48.P04

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation mixed)

/-- Bennett--DiVincenzo--Smolin, PDF pp.2,4: the same protocol covers every
pattern of t erasures. Its n forward slots first allow EPR distribution; the
subsequent classical feedback and teleportation are free. The zero-qubit
logical register is retained when t=n. -/
theorem perfectAdaptiveErasure (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    ∃ P : TwoWayQubitCode 2 3 n (n-t),
      (((n-t : ℕ) : ℝ) / n = 1-(t : ℝ)/n) ∧
      ∀ S : Finset (Fin n), S.card = t →
        ∀ psi : EuclideanSpace ℂ (Qubits (n-t)), IsState psi →
          effectProb (pureDensity psi) (P.output (erasureSchedule S) (pureDensity psi)) = 1 := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P04
