-- Prove2me | Theorems.Thm_SkutellaCQP_MaxCut_theorem_2_6_b
-- name    : SkutellaCQP.MaxCut.theorem_2_6_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:26.453012+00:00
-- url     : https://prove2.me/theorems/85e8f372-545f-4d56-8c36-36d2a6655e5b
-- title:
--   Theorem 2.6 b), p. 12 — uniform independent random assignment is a (3/2 − 1/(2m))-approximation for P | | Σ wⱼCⱼ
-- statement:
--   Consider $n$ jobs with processing times $p_j>0$ and weights $w_j\ge0$ on $m\ge1$ identical parallel machines. Assign each job independently and uniformly at random to one of the $m$ machines, and sequence each machine by Smith's order $\prec$. Every assignment $\sigma$ then has probability $(1/m)^n$, and the expected value of the schedule satisfies
--   $$
--   \mathbb E\Big[\sum_j w_jC_j\Big]=\sum_{\sigma}\Big(\frac1m\Big)^n\sum_j w_jC_j(\sigma)\le\Big(\frac32-\frac1{2m}\Big)\sum_j w_jC_j(\tau)
--   $$
--   for every assignment $\tau$, i.e. the expectation is within a factor $\tfrac32-\tfrac1{2m}$ of the optimum $Z^*$.
--
--   This is the guarantee of the simplest randomized algorithm for $P\,|\,|\sum w_jC_j$; it coincides with randomized rounding of the (CQP) optimum $\bar a$ of Lemma 2.5.
--
--   **Formalization Note** The random assignment is the uniform distribution on the $m^n$ assignments, written as an explicit finite sum. $Z^*$ is the minimum over assignments, so the bound is stated against every assignment $\tau$.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 12, Theorem 2.6 b) (proof on pp. 12–13)

import Mathlib
import Definitions.Def_SkutellaCQP_MaxCut_Setting

namespace SkutellaCQP.MaxCut

open Finset

/-- Theorem 2.6 b), p. 12. Assigning each job independently and uniformly at random to one of the
`m` identical machines (each assignment `σ` has probability `(1/m)^n`) gives an expected value
`∑_j w_j C_j` at most `(3/2 − 1/(2m))` times the value of every schedule. -/
theorem theorem_2_6_b {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hm : 0 < m) :
    ∀ τ : Fin n → Fin m,
      ∑ σ : Fin n → Fin m, (1 / (m : ℝ)) ^ n * val p w σ ≤
        (3 / 2 - 1 / (2 * (m : ℝ))) * val p w τ := by sorry

end SkutellaCQP.MaxCut
