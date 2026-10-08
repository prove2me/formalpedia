-- Prove2me | Theorems.Thm_WeightedMajority_General_log_display
-- name    : WeightedMajority.General.log_display
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:47.366633+00:00
-- url     : https://prove2.me/theorems/ad70cbd0-fe3f-40b2-b9aa-2d7aef66a541
-- title:
--   §5, p. 235 — the sum of log(1 − (1−β)|γ − ρ|) over update trials is at most m log(1/2 + β/2)
-- statement:
--   Let $0 \le \beta < 1$ and consider a run of WMG with parameter $\beta$ on a pool with predictions $x_{k,i} \in [0,1]$ and binary labels $\rho_k$, with weighted averages $\gamma_k$ and $m$ mistakes. Suppose that it is not the case that $\beta = 0$ and $|\gamma_k - \rho_k| = 1$ for some update trial $k$. Then, writing $U$ for the set of update trials and $M \subseteq U$ for the set of trials in which WMG makes a mistake,
--
--   $$
--   \sum_{k \in U} \ln\bigl(1 - (1-\beta)|\gamma_k - \rho_k|\bigr) \;\le\; \sum_{k \in M} \ln\bigl(1 - (1-\beta)|\gamma_k - \rho_k|\bigr) \;\le\; m \ln\Bigl(\frac12 + \frac12\beta\Bigr).
--   $$
--
--   This display, combined with Lemma 5.2 of the paper ($\ln(w_{\mathrm{fin}}/w_{\mathrm{init}})$ is at most the left-hand sum), gives Theorem 5.1.
--
--   **Formalization Note** The paper writes "log" with the base left open; the inequality does not depend on the base, and the natural logarithm `Real.log` is used. The excluded case is the one in which a factor $1 - (1-\beta)|\gamma_k - \rho_k|$ vanishes, where the paper's logarithm is $-\infty$ and Lean's `Real.log 0 = 0` would make the second inequality false.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 235, Section 5, proof of Theorem 5.1 (unnumbered display)

import Mathlib
import Definitions.Def_WeightedMajority_General_WMGRun

namespace WeightedMajority.General

/-- §5, p. 235 (proof of Theorem 5.1): outside the case `β = 0` and `|γ - ρ| = 1` in some update
trial, the sum over the update trials of `log (1 - (1 - β) |γ - ρ|)` is at most the same sum over
the mistake trials, which is at most `m log (1/2 + β/2)`. -/
theorem log_display {n T : ℕ} {β : ℝ} {x : Fin T → Fin n → ℝ} {ρ : Fin T → ℝ}
    {w : ℕ → Fin n → ℝ} {pred : Fin T → ℝ} {upd : Fin T → Bool} {F : Fin T → Fin n → ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hrun : IsWMGRun β x ρ w pred upd F)
    (hnot : ¬ (β = 0 ∧ ∃ k, upd k = true ∧ |gamma x w k - ρ k| = 1)) :
    (∑ k ∈ Finset.univ.filter (fun k => upd k = true),
        Real.log (1 - (1 - β) * |gamma x w k - ρ k|)) ≤
      (∑ k ∈ Finset.univ.filter (fun k => upd k = true ∧ pred k ≠ ρ k),
        Real.log (1 - (1 - β) * |gamma x w k - ρ k|)) ∧
    (∑ k ∈ Finset.univ.filter (fun k => upd k = true ∧ pred k ≠ ρ k),
        Real.log (1 - (1 - β) * |gamma x w k - ρ k|)) ≤
      (mistakeCount pred ρ : ℝ) * Real.log (1 / 2 + 1 / 2 * β) := by sorry

end WeightedMajority.General
