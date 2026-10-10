-- Prove2me | Theorems.Thm_ReusablePricing_DPC_eq_EC15
-- name    : ReusablePricing.DPC.eq_EC15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:17.667191+00:00
-- url     : https://prove2.me/theorems/118a47d5-ec02-442f-a5b5-1901ddb7ad9b
-- title:
--   (EC.15), ec7 — E[exp{±γ Σ_{cycle b} Δˢ_j}] ≤ exp{min{maxᵢCᵢ, n}·γ²} for γ ∈ (0, 1]
-- statement:
--   Consider the basic reusable-resource model under its standing hypotheses and run DPC($\epsilon$) with $\epsilon > 0$. Let $\Delta^s_j = D^s_j - \lambda^s_j$. For every service type $j$, every service cycle $b \in [1, T/n]$ and every $\gamma \in (0,1]$,
--   $$\mathbf E\Big[\exp\Big\{\gamma \sum_{s=(b-1)n+1}^{bn} \Delta^s_j\Big\}\Big] \le \exp\big\{\min\{\max_i C_i, n\}\cdot\gamma^2\big\},$$
--   and the same bound holds with $-\gamma$ in place of $\gamma$.
--
--   This bound on the moment generating function of the cumulative demand error over one service cycle is the input to the maximal inequality in Lemma EC.2.
--
--   **Formalization Note.** The bound with $-\gamma$ is the page's sentence "similar arguments can also be applied to $\mathbf E[\exp\{-\gamma\sum\Delta^s_j\}]$", stated explicitly. $\epsilon > 0$ is the paper's standing range for the DPC parameter (p. 12).
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), p. ec7, (EC.15) and the sentence after it

import Mathlib
import Definitions.Def_ReusablePricing_DPC_Model
import Definitions.Def_ReusablePricing_DPC_Control

namespace ReusablePricing.DPC

open Finset

/-- (EC.15), ec7, with the mirror bound the page asserts right after it: for every service type
`j`, cycle `b ∈ [1, T/n]` and `γ ∈ (0, 1]`, under DPC(ε) with `ε > 0`,
`E[exp{± γ ∑_{s=(b-1)n+1}^{bn} Δ^s_j}] ≤ exp{min{max_i C_i, n} γ²}`. -/
theorem eq_EC15 (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ) (ε : ℝ)
    (hP : P.Standing φL φU Ψ R nl) (hε : 0 < ε)
    (j : Fin P.J) (b : ℕ) (hb : b ∈ Icc 1 (P.T / P.n)) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    P.E ε nl (fun ω => Real.exp (γ * ∑ s ∈ Icc ((b - 1) * P.n + 1) (b * P.n),
        P.Delta ε nl s ω j)) ≤ Real.exp (P.minCapN * γ ^ 2) ∧
    P.E ε nl (fun ω => Real.exp (-γ * ∑ s ∈ Icc ((b - 1) * P.n + 1) (b * P.n),
        P.Delta ε nl s ω j)) ≤ Real.exp (P.minCapN * γ ^ 2) := by sorry

end ReusablePricing.DPC
