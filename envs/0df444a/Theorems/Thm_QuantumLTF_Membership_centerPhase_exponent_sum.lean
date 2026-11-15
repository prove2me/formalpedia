-- Prove2me | Theorems.Thm_QuantumLTF_Membership_centerPhase_exponent_sum
-- name    : QuantumLTF.Membership.centerPhase_exponent_sum
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-14T21:51:50.646239+00:00
-- url     : https://prove2.me/theorems/2144f54a-c50c-4291-93d9-1317f336761f
-- title:
--   Sum of centered-grid wire phases
-- statement:
--   Let $N=2^b$ and $c=-1/2+1/(2N)$. For a $b$-bit basis label $z$, the sum of the wire-dependent phases $c2^{b-1-i}$ on active wires, together with the equal per-wire shares of the constant phase, is $c bitsToNat(z)+Nc^2/2$. The statement also covers $b=0$, where both sides vanish.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 3.3, p. 27 (PDF p. 28), Eqs. (44)–(48).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QuantumLTF.Membership

open QAlgorithms

/-- The sum of all per-wire centered-grid phases collapses to the phase of the represented integer. -/
theorem centerPhase_exponent_sum (b : ℕ) (z : Qubits b) :
    let N : ℂ := (2 : ℂ) ^ b
    let c : ℂ := -(1 / 2) + 1 / (2 * N)
    (∑ i : Fin b,
      ((if z i then c * (2 : ℂ) ^ (b - 1 - i.1) else 0) +
        N * c ^ 2 / (2 * b))) =
      c * (bitsToNat z : ℂ) + N * c ^ 2 / 2 := by sorry

end QuantumLTF.Membership
