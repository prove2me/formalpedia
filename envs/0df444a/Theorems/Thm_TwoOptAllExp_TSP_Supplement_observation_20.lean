-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_observation_20
-- name    : TwoOptAllExp.TSP.Supplement.observation_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T04:48:50.408183+00:00
-- url     : https://prove2.me/theorems/5e9a6ed2-593b-468a-8442-71ad3651d1b5
-- title:
--   Observation 20 — the three-block recursions of $\Omega_n$ and $\bar\Omega_n$
-- statement:
--   For the strings of Section 5 obtained from $R_n$ by the insertion rule: $\Omega_0=\bar\Omega_0=R_0$, and for $n\ge1$
--
--   $$\Omega_n=(v_{n,1},v_{n,2},\rho_n^{(1)},\Omega_{n-1},\alpha_n,v_{n,3},v_{n,4},\rho_n^{(2)},\bar\Omega_{n-1},\alpha_n,v_{n,5},v_{n,6},\rho_n^{(3)},\Omega_{n-1},\alpha_n,v_{n,7},v_{n,8}),$$
--   $$\bar\Omega_n=(v_{n,1},v_{n,2},\rho_n^{(4)},\bar\Omega_{n-1},\alpha_n,v_{n,3},v_{n,4},\rho_n^{(5)},\Omega_{n-1},\alpha_n,v_{n,5},v_{n,6},\rho_n^{(0)},\bar\Omega_{n-1},\alpha_n,v_{n,7},v_{n,8}).$$
--
--   The recursion is the form of the canonical sequence used in the induction of Lemma 24.
--
--   Differences from the source:
--   - encoding: for n ≥ 1, Ω_{n−1} → n − 1 in ℕ under the hypothesis 1 ≤ n; reason: no truncation occurs
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Observation 20, p. 31

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA232

namespace TwoOptAllExp.TSP.Supplement

open MCA232 MCA232.Vx

/-- **Observation 20** (p. 31). `Ω_0 = Ω̄_0 = R_0`, and for `n ≥ 1`
`Ω_n = (v_{n,1}, v_{n,2}, ρ_n^{(1)}, Ω_{n-1}, α_n, v_{n,3}, v_{n,4}, ρ_n^{(2)}, Ω̄_{n-1}, α_n, v_{n,5}, v_{n,6}, ρ_n^{(3)}, Ω_{n-1}, α_n, v_{n,7}, v_{n,8})`,
`Ω̄_n = (v_{n,1}, v_{n,2}, ρ_n^{(4)}, Ω̄_{n-1}, α_n, v_{n,3}, v_{n,4}, ρ_n^{(5)}, Ω_{n-1}, α_n, v_{n,5}, v_{n,6}, ρ_n^{(0)}, Ω̄_{n-1}, α_n, v_{n,7}, v_{n,8})`. -/
theorem observation_20 :
    Omega 0 = R 0 ∧ OmegaBar 0 = R 0 ∧
    ∀ n : ℕ, 1 ≤ n →
      Omega n = [v n 1, v n 2] ++ rho n 1 ++ Omega (n - 1) ++ alpha n ++
        [v n 3, v n 4] ++ rho n 2 ++ OmegaBar (n - 1) ++ alpha n ++
        [v n 5, v n 6] ++ rho n 3 ++ Omega (n - 1) ++ alpha n ++ [v n 7, v n 8] ∧
      OmegaBar n = [v n 1, v n 2] ++ rho n 4 ++ OmegaBar (n - 1) ++ alpha n ++
        [v n 3, v n 4] ++ rho n 5 ++ Omega (n - 1) ++ alpha n ++
        [v n 5, v n 6] ++ rho n 0 ++ OmegaBar (n - 1) ++ alpha n ++ [v n 7, v n 8] := by sorry

end TwoOptAllExp.TSP.Supplement
