-- Prove2me | Theorems.Thm_WeightedMajority_General_theorem_5_1
-- name    : WeightedMajority.General.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:52.166468+00:00
-- url     : https://prove2.me/theorems/e7435e57-ee9f-4930-afff-dd13054a16e3
-- title:
--   Theorem 5.1 — WMG makes at most log(w_init/w_fin)/log(2/(1+β)) mistakes
-- statement:
--   Let $0 \le \beta < 1$. Run the master algorithm WMG with parameter $\beta$ on a pool of $n$ prediction algorithms, whose predictions $x_{k,i}$ lie in $[0,1]$, over any finite sequence of trials with binary labels $\rho_k \in \{0,1\}$; WMG may update in every trial or only in the trials in which it makes a mistake, may break ties at $\gamma_k = 1/2$ either way, and may use any update factors allowed by (5.1). Let $w_{\mathrm{init}}$ and $w_{\mathrm{fin}}$ be the total initial and final weights of the pool, and let $m$ be the number of mistakes of WMG. If $w_{\mathrm{fin}} > 0$, then
--
--   $$
--   m \le \frac{\ln(w_{\mathrm{init}}/w_{\mathrm{fin}})}{\ln\bigl(2/(1+\beta)\bigr)} .
--   $$
--
--   This is the mistake bound of Theorem 2.1 for the binary algorithm WM, extended to pools whose members predict numbers in $[0,1]$. With equal initial weights it yields Corollary 5.1: the number of mistakes is at most $(\log n + m_i \log(1/\beta))/\log(2/(1+\beta))$ for every pool member $i$ with total absolute loss $m_i$.
--
--   **Formalization Note** The paper writes the bound as a ratio of logarithms with the base omitted; the ratio does not depend on the base, and `Real.log` is used. When $w_{\mathrm{fin}} = 0$ (possible only if $\beta = 0$) the paper's bound is $+\infty$, and Lean's `Real.log` and division conventions would give a false literal statement; this case is excluded by the hypothesis $w_{\mathrm{fin}} > 0$. The run is the relation `IsWMGRun`, so the bound is asserted for every tie-breaking, every update flag that is set on all mistake trials, and every factor in (5.1).
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), pp. 234–235, Theorem 5.1

import Mathlib
import Definitions.Def_WeightedMajority_General_WMGRun

namespace WeightedMajority.General

/-- Theorem 5.1 (pp. 234–235): for every run of WMG with `0 ≤ β < 1` on a sequence of `T` trials
with binary labels and pool predictions in `[0, 1]` (updating in every trial, only in mistake
trials, or in any set of trials containing the mistake trials), the number `m` of mistakes
satisfies `m ≤ log (w_init / w_fin) / log (2 / (1 + β))`, provided `w_fin > 0`
(for `w_fin = 0` the paper's bound is `+∞`). -/
theorem theorem_5_1 {n T : ℕ} {β : ℝ} {x : Fin T → Fin n → ℝ} {ρ : Fin T → ℝ}
    {w : ℕ → Fin n → ℝ} {pred : Fin T → ℝ} {upd : Fin T → Bool} {F : Fin T → Fin n → ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hrun : IsWMGRun β x ρ w pred upd F)
    (hfin : 0 < WeightedMajority.Basic.totalWeight w T) :
    (mistakeCount pred ρ : ℝ) ≤
      Real.log (WeightedMajority.Basic.totalWeight w 0 / WeightedMajority.Basic.totalWeight w T) / Real.log (2 / (1 + β)) := by sorry

end WeightedMajority.General
