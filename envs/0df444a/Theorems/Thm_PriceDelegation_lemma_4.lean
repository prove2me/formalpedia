-- Prove2me | Theorems.Thm_PriceDelegation_lemma_4
-- name    : PriceDelegation.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:27.836275+00:00
-- url     : https://prove2.me/theorems/778d7429-a30a-4350-b9d4-a3f49d040a58
-- title:
--   Lemma 4 — $\Delta$ has a unique zero $\lambda^{p-l}$, and $\Delta(\lambda)\ge0$ iff $\lambda\le\lambda^{p-l}$
-- statement:
--   Let $\psi>0$, let the valuation satisfy Assumptions 1 and 2, and let $N\ge1$. For $\lambda\ge0$ set
--   $$
--   \Delta(\lambda)=N\big(E[(V-\lambda)^+]-\psi\big)-N\max_{\varphi>0}(\varphi-\lambda)\bar F(\varphi).
--   $$
--   Then there is exactly one $\lambda^{p-l}\ge0$ with $\Delta(\lambda^{p-l})=0$, and for every $\lambda\ge0$,
--   $$\Delta(\lambda)\ge0\iff\lambda\le\lambda^{p-l}.$$
--
--   At the multiplier $\lambda^{p-l}$ the firm is indifferent between inducing learning and not; it separates the full-learning, partial-learning and no-learning regimes of Lemma 5 and Proposition 4.
--
--   Differences from the source:
--   - reading: $N$ customers, with $K\le N$ and multiple units → $N\ge1$; reason: for $N=0$, $\Delta\equiv0$ and the zero is not unique; the paper's $N\ge K\ge1$
--   - reading: E[V] < ∞ is not stated → the valuation law has $\int_0^\infty v f(v)\,dv<\infty$; reason: $J^{FB}=E[V]-\psi$ and Assumption 1 compare finite numbers (p.11), and every maximum of §4.3 needs $\varphi\bar F(\varphi)\to0$
--   - encoding: a continuous random variable with density $f$ and support $(0,\infty)$ (p.8) → a measurable density vanishing on $(-\infty,0]$ with positive mass on every interval $[a,b]\subseteq[0,\infty)$, $a<b$; reason: this is what support $(0,\infty)$ means for the law; no condition on $f$ beyond a density is added
-- source:
--   Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), Lemma 4, p.25

import Mathlib
import Definitions.Def_PriceDelegation_Valuation
import Definitions.Def_PriceDelegation_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PriceDelegation

/-- Lemma 4 (Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of
Sept. 22, 2021), p.25). Let `∆(λ) = N · (E[(V − λ)⁺] − ψ) − N · max_{φ>0} (φ − λ) F̄(φ)` for `λ ≥ 0`.
There is a unique `λ^{p-l} ≥ 0` with `∆(λ^{p-l}) = 0`, and for `λ ≥ 0`, `∆(λ) ≥ 0` if and only if
`λ ≤ λ^{p-l}`. Standing assumptions: `ψ > 0` (p.9), Assumption 1 (p.11), Assumption 2 (p.20),
`N ≥ 1` customers. -/
theorem lemma_4 (V : Valuation) {ψ : ℝ} (hψ : 0 < ψ) {N : ℕ} (hN : 0 < N)
    (hA1 : Assumption1 V ψ) (hA2 : Assumption2 V) :
    (∃! lp : ℝ, 0 ≤ lp ∧ Delta V ψ N lp = 0) ∧
      ∀ lp : ℝ, 0 ≤ lp → Delta V ψ N lp = 0 →
        ∀ lam : ℝ, 0 ≤ lam → (0 ≤ Delta V ψ N lam ↔ lam ≤ lp) := by sorry

end PriceDelegation
