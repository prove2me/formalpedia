-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_discard_copies_channel
-- name    : QuantumLTF.Membership.Supplement.discard_copies_channel
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-24T23:22:26.61174+00:00
-- url     : https://prove2.me/theorems/ae60f715-f189-41d7-93fa-a487ff2d68d5
-- title:
--   Discarding surplus direction-state copies by a fixed positive trace-preserving map
-- statement:
--   Let $K,L,n,s$ be nonnegative integers with $n\le 2^s$, so an $s$-qubit register can encode an $n$-dimensional direction. There is one complex-linear positive, trace-preserving map $\Phi$ from $K+L$ registers to $K$ registers such that, for every real unit vector $w$,
--
--   $$\Phi\bigl((|w\rangle\langle w|)^{\otimes(K+L)}\bigr)=(|w\rangle\langle w|)^{\otimes K}.$$
--
--   The map is independent of $w$ and acts on the explicit public direction-state register layout. This is the discard identity used after occupation decoding in Theorem 5.4; the efficient decoder remains a separate construction.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5.3, Theorem 5.4, discarding surplus copies after the occupation isometry.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_Supplement_dirTensorPow
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped ComplexOrder

theorem QuantumLTF.Membership.Supplement.discard_copies_channel (n K L s : ℕ) (hs : n ≤ 2^s) :
    ∃ Φ : Matrix (Qubits ((K+L)*s)) (Qubits ((K+L)*s)) ℂ →ₗ[ℂ]
        Matrix (Qubits (K*s)) (Qubits (K*s)) ℂ,
      (∀ A, A.PosSemidef → (Φ A).PosSemidef) ∧
      (∀ A, (Φ A).trace = A.trace) ∧
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
        Φ (dirTensorPow s (K+L) w) = dirTensorPow s K w := by sorry
