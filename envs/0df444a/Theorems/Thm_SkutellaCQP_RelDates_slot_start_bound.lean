-- Prove2me | Theorems.Thm_SkutellaCQP_RelDates_slot_start_bound
-- name    : SkutellaCQP.RelDates.slot_start_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:21.675117+00:00
-- url     : https://prove2.me/theorems/76819ae4-c828-48c7-99fd-69328e1eb02e
-- title:
--   §3.3, proof of Lemma 3.5, p. 20 — E_{j↦i_k}[s_{i_k}] ≤ 2ρ_{i_k}
-- statement:
--   Let $a$ be feasible for (CQP) and let $\bar a$ be obtained from $a$ by randomized rounding with pairwise independent choices for the jobs. Fix a job $j$ and a time slot $i_k$. Let $s_{i_k}$ be the starting time of slot $i_k$ in the schedule built from $\bar a$ by (15)–(16). Then the conditional expectation of $s_{i_k}$, given that $j$ is assigned to $i_k$, is at most $2\rho_{i_k}$. Multiplied by $\Pr[j \mapsto i_k] = a_{i_kj}$:
--   $$\sum_{\tau:\ \tau(j) = i_k} \mu(\tau)\, s_{i_k}(\tau) \;\le\; 2\rho_{i_k}\, a_{i_kj}.$$
--
--   This is the only place where the capacity constraints (21) enter the analysis of the 2-approximation.
--
--   **Formalization Note.** The page's $E_{j \mapsto i_k}[s_{i_k}] \le 2\rho_{i_k}$ is stated multiplied through by $\Pr[j \mapsto i_k] = a_{i_kj}$, which avoids dividing by a probability that may be $0$; for $a_{i_kj} > 0$ the two forms are equivalent. The bound uses $\rho_{i_1} \ge 0$, i.e. the standing assumption $r_{ij} \ge 0$.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 20, §3.3, proof of Lemma 3.5, first display

import Mathlib
import Definitions.Def_SkutellaCQP_RelDates_Setting

namespace SkutellaCQP.RelDates

open Finset

/-- Proof of Lemma 3.5, p. 20: `E_{j↦i_k}[s_{i_k}] ≤ 2ρ_{i_k}`, multiplied through by
`Pr[j ↦ i_k] = a_{i_k j}`. -/
theorem slot_start_bound {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (a : Fin m → Fin n → Fin n → ℝ) (ha : CQPFeasible p r a)
    (μ : (Fin n → Fin m × Fin n) → ℝ) (hμ : IsPairwiseRounding a μ)
    (j : Fin n) (i : Fin m) (k : Fin n) :
    ∑ τ ∈ univ.filter (fun τ : Fin n → Fin m × Fin n => τ j = (i, k)),
        μ τ * sStart p r (slotInd τ) i k ≤ 2 * rho r i k * a i k j := by sorry

end SkutellaCQP.RelDates
