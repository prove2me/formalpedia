-- Prove2me | Theorems.Thm_TaoFivePrimes_euler_mascheroni_exp_bound
-- name    : TaoFivePrimes.euler_mascheroni_exp_bound
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T09:14:13.852863+00:00
-- url     : https://prove2.me/theorems/1fe16460-4b7c-4563-99ce-bcb52fadf98f
-- title:
--   $e^\gamma < 1.7857$
-- statement:
--   The exponential of the Euler--Mascheroni constant satisfies
--   $$e^{\gamma} \;<\; 1.7857.$$
--   (True value: $e^{\gamma} = 1.78107\ldots$.) This is the numerical rounding step in Rosser--Schoenfeld's proof of Lemma 15 (where $1.4\, e^{\gamma} < 5/2$ is used).
-- source:
--   Numerical fact on the Euler–Mascheroni constant γ = 0.5772156649…; used in J.B. Rosser, L. Schoenfeld, Illinois J. Math. 6 (1962), §9, p. 89, Lemma 15 proof (where 1.4 e^γ < 5/2).

import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem euler_mascheroni_exp_bound :
    Real.exp Real.eulerMascheroniConstant < 1.7857 := by sorry
end TaoFivePrimes
