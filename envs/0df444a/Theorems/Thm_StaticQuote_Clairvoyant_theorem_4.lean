-- Prove2me | Theorems.Thm_StaticQuote_Clairvoyant_theorem_4
-- name    : StaticQuote.Clairvoyant.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:19.447256+00:00
-- url     : https://prove2.me/theorems/00536fac-e7ed-45d3-b905-6ff8d7600924
-- title:
--   Theorem 4, p. 18 — C^π ≥ λ E[γ_{1:N}/N] for every FCFS schedule π and every N ≥ 1
-- statement:
--   Consider the GI/G/1 queue with common quote time $\delta$ under the standing assumptions of the model: i.i.d. inter-arrival times $T_n$ with mean $1/\lambda$, i.i.d. service times $x_n$ with mean $1/\mu$, all mutually independent, and $\lambda<\mu$. Customer $n$ arrives at $t_n=T_1+\cdots+T_n$, is due at $d_n=t_n+\delta$, and pays $g(D_n-d_n)$ with $g(\xi)=c_e(-\xi)^+ + c_d(\xi)^+$. Let $\gamma_{1:N}(\omega)$ be the perfectly-clairvoyant cost (12) of the first $N$ customers. Then for every FCFS-feasible schedule $y$, with long-run average cost $C(y)$ in the per-customer form (4), and every $N\ge1$,
--   $$C(y) \ge \lambda\,\mathbb E\Big[\frac{\gamma_{1:N}(\omega)}{N}\Big].$$
--
--   In the paper this reads $C^{\pi^*}\ge\lambda\,\mathbb E[\gamma_{1:N}/N]$ for all $N\in\mathbb N$. A deterministic clairvoyant problem over any finite number of customers, estimated by Monte Carlo simulation, therefore gives a valid lower bound on the optimal long-run average cost.
--
--   **Formalization Note.** The paper's $C^{\pi^*}$ presupposes an optimal policy whose existence is not shown, and its proof bounds $C^\pi$ for every $\pi$ in its class $\Pi$. The statement here bounds $C(y)$ for every schedule that is FCFS-feasible on every sample path. That class contains every policy of $\Pi$, so the statement implies the paper's for $\pi^*$ whenever it exists and for $\inf_{\pi\in\Pi}C^\pi$ in any case. The Loynes stable class $\Pi$ itself is not modelled. $C$ is defined by form (4); $\gamma$, the expectations and the $\limsup$ take values in $[0,\infty]$. $N\ge1$ because the paper's $\mathbb N$ starts at $1$.
-- source:
--   Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 18, Theorem 4

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting

open MeasureTheory Filter
open scoped ENNReal

namespace StaticQuote.Clairvoyant

/-- Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 18, Theorem 4: `C^{π∗} ≥ λ E[γ_{1:N}(ω)/N]` for all `N ∈ ℕ`.

**Formalization Notes.**
* "`C^{π∗} ≥ …`" is stated as "`C^π ≥ …` for every FCFS-feasible schedule `y`": the existence of an
  optimal π∗ is never shown in the paper, and its proof bounds `C^π` for every π ∈ Π ((14)). Every
  policy of the paper's class Π gives an FCFS-feasible schedule, so this implies the page's statement
  for π∗ whenever it exists, and for `inf_{π ∈ Π} C^π` in any case. The paper's Loynes stable class Π
  is not modelled (its L¹ convergence requirement may leave it empty).
* `C^π` is `Model.cost`, the per-customer form (4) (p. 11); λ = `Model.rate μ` = 1/E[T_1].
* `γ_{1:N}` is the `ℝ≥0∞` infimum (12); expectations are `lintegral`s; the lim sup in `cost` is in
  `ℝ≥0∞`.
* `N ≥ 1` (the paper's ℕ starts at 1). -/
theorem theorem_4 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Model Ω)
    (hQ : Q.Standing μ) (y : ℕ → Ω → ℝ) (hy : Q.IsFCFSSchedule y) (N : ℕ) (hN : 1 ≤ N) :
    ENNReal.ofReal (Q.rate μ) * ∫⁻ ω, Q.gamma 1 N ω / (N : ℝ≥0∞) ∂μ ≤ Q.cost μ y := by sorry

end StaticQuote.Clairvoyant
