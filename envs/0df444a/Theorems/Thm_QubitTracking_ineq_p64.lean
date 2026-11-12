-- Prove2me | Theorems.Thm_QubitTracking_ineq_p64
-- name    : QubitTracking.ineq_p64
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:26:40.073334+00:00
-- url     : https://prove2.me/theorems/cce758af-9af5-4010-8939-ec40a90891c6
-- title:
--   Proof of Theorem 9.3, p.64 — $1-\eta^{2/\gamma}=1-\exp(-2\log(1/\eta)/\gamma)\le 2\log(1/\eta)/\gamma$
-- statement:
--   For $0<\eta\le1$ and $\gamma>0$,
--   $$1-\eta^{2/\gamma}=1-\exp\Big(-\frac{2\log(1/\eta)}{\gamma}\Big)\le\frac{2\log(1/\eta)}{\gamma}.$$
--
--   This converts the bound $1-O((1-q_{i^\star}q_{i^\star+1})^{1/4})$ of Theorem 7.9 into the bound $1-O((\log(1/\eta)/\gamma)^{1/4})$ of Theorems 9.3 and 9.6.
--
--   Differences from the source:
--   - generalization: γ a positive integer (repetition factor) → γ any positive real; reason: the identity and the inequality hold for real γ > 0, which include the integers
--   - encoding: log → the natural logarithm; reason: the proof writes η^{2/γ} = exp(−2 log(1/η)/γ), which is the natural logarithm
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), proof of Theorem 9.3, p.64, displayed inequality (reused in the proof of Theorem 9.6, p.68)

import Mathlib

set_option autoImplicit false

namespace QubitTracking

/-- **The inequality `1 − η^{2/γ} ≤ 2 log(1/η)/γ`** (Bartusek, Huang, Orshansky, Yuen, *How To Track
Qubits Through Space and Time*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), proof of
Theorem 9.3, p.64, displayed inequality; reused in the proof of Theorem 9.6, p.68): for
`0 < η ≤ 1` and `γ > 0`,
`1 − η^{2/γ} = 1 − exp(−2 log(1/η)/γ) ≤ 2 log(1/η)/γ`.

**Formalization Note** `log` is the natural logarithm and `η^{2/γ}` the real power; `γ` is real
(the proof uses integers `γ ≥ 1`). -/
theorem ineq_p64 (η γ : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hγ : 0 < γ) :
    1 - η ^ (2 / γ) = 1 - Real.exp (-(2 * Real.log (1 / η) / γ)) ∧
      1 - Real.exp (-(2 * Real.log (1 / η) / γ)) ≤ 2 * Real.log (1 / η) / γ := by sorry

end QubitTracking
