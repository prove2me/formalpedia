-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_security
-- name    : PauliUnclonable531.Pauli.security
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:26.225998+00:00
-- url     : https://prove2.me/theorems/53eb4c0e-8d00-4cf5-ba4c-e28dbab03bbc
-- title:
--   Theorem 4.1 — the exact all-attacks security bound
-- statement:
--   For every n≥1 and every information-theoretic pre-key splitting attack with arbitrary nonzero finite output registers B and C, the concrete Section 3 scheme satisfies
--
--   $$\Pr[b_B=b_C=b]\le\frac12+\frac12\sqrt{\frac{2^n}{4^n-1}}.$$
--
--   The key and challenge bit are independent and exactly uniform. The splitter is an arbitrary CPTP channel, while the local post-key measurements are arbitrary binary POVMs. This is the fixed-(0,1) game of Theorem 4.1 and Remark 2.12; the headline also quantifies over randomized adversarial message pairs.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Theorem 4.1, p.17, Eq. (17)

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Game

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Theorem 4.1, Eq. (17), p.17, in the fixed-message game of Remark 2.12. -/
theorem security {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Attack n B C) :
    win a ≤ 1/2 + (1/2) * Real.sqrt ((2 : ℝ)^n / ((4 : ℝ)^n - 1)) := by sorry

end PauliUnclonable531.Pauli
