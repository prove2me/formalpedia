-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_polynomial_identities
-- name    : SuperactivatedCheating.StateConversion.polynomial_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:20.631195+00:00
-- url     : https://prove2.me/theorems/77198f42-f797-4204-83bc-027e7068245b
-- title:
--   Proof of Theorem 11, pp. 15–16 — the polynomials S, P and the expansions of S² and S³
-- statement:
--   Over $\mathbb Z[x]$ let $S(x)=1+x+2x^2-x^3+2x^4+x^5$ and $P(x)=(1+x)S(x)$. Then $P(x)=1+2x+3x^2+x^3+x^4+3x^5+x^6$; $S$ has a negative coefficient; $S(x)^2=1+2x+5x^2+2x^3+6x^4+2x^5+11x^6+2x^8+4x^9+x^{10}$; $S(x)^3=1+3x+9x^2+10x^3+18x^4+12x^5+35x^6+18x^7+36x^8+5x^9+33x^{10}+18x^{11}+2x^{12}+9x^{13}+6x^{14}+x^{15}$; and every coefficient of $S^2$ and of $S^3$ is nonnegative.
--
--   Differences from the source:
--   - encoding: polynomials in x → Polynomial ℤ; reason: all coefficients are integers; same identities
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/399.pdf, proof of Theorem 11, pp. 15–16

import Mathlib
import Definitions.Def_SuperactivatedCheating_StateConversion_GameSC

open Polynomial

namespace SuperactivatedCheating.StateConversion

/-- Proof of Theorem 11, pp. 15–16: `P = (1 + x) S` expands as printed, `S` has a negative
coefficient, and `S²`, `S³` expand as printed, with nonnegative coefficients. -/
theorem polynomial_identities :
    polyP = 1 + 2 * X + 3 * X ^ 2 + X ^ 3 + X ^ 4 + 3 * X ^ 5 + X ^ 6 ∧
    (∃ i, polyS.coeff i < 0) ∧
    polyS ^ 2 = 1 + 2 * X + 5 * X ^ 2 + 2 * X ^ 3 + 6 * X ^ 4 + 2 * X ^ 5 + 11 * X ^ 6 +
      2 * X ^ 8 + 4 * X ^ 9 + X ^ 10 ∧
    polyS ^ 3 = 1 + 3 * X + 9 * X ^ 2 + 10 * X ^ 3 + 18 * X ^ 4 + 12 * X ^ 5 + 35 * X ^ 6 +
      18 * X ^ 7 + 36 * X ^ 8 + 5 * X ^ 9 + 33 * X ^ 10 + 18 * X ^ 11 + 2 * X ^ 12 +
      9 * X ^ 13 + 6 * X ^ 14 + X ^ 15 ∧
    (∀ i, 0 ≤ (polyS ^ 2).coeff i) ∧ (∀ i, 0 ≤ (polyS ^ 3).coeff i) := by sorry

end SuperactivatedCheating.StateConversion
