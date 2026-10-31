-- Prove2me | Theorems.Thm_TabooRegen_chernoff_tail
-- name    : TabooRegen.chernoff_tail
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:26.916244+00:00
-- url     : https://prove2.me/theorems/e25b6970-f6a8-41f0-a2fe-57b824e4c871
-- title:
--   Theorem 2, proof, p.287 — Chernoff bound on $T(\ell)$ under $P^*$
-- statement:
--   Let $F$ be a probability measure on $[0,\infty)$ with $\int e^{\varepsilon_0y}F(dy)<\infty$ for some $\varepsilon_0>0$, and mean $m$. Write $F^{*\ell}$ for its $\ell$-fold convolution and $\psi(\varepsilon)=\log\int e^{\varepsilon y}F(dy)$. Then:
--
--   1. for every $\varepsilon\ge0$, $\ell\ge0$ and $x$,
--   $$
--   F^{*\ell}\big((x,\infty)\big)\le e^{-\varepsilon x}\Big(\int e^{\varepsilon y}F(dy)\Big)^{\ell}=\exp\big(-\varepsilon x+\ell\psi(\varepsilon)\big);
--   $$
--   2. for every $\eta\in(0,1)$ there is $\delta>0$ such that for all $t\ge0$ and $\ell\ge0$ with $m\ell\le(1-\eta)t$,
--   $$
--   F^{*\ell}\Big(\big((1-\tfrac\eta2)t,\infty\big)\Big)\le e^{-\delta t}.
--   $$
--
--   In the proof of Theorem 2, $F=\tilde G$ (mean $\lambda^{-1}$) and $F^{*\ell}$ is the law of $T(\ell)$ under $P^*$: with at most $\lambda(1-\eta)t$ tabooed cycles, their total length exceeds $(1-\eta/2)t$ only with exponentially small probability.
--
--   Differences from the source:
--   - generalization: $P^*(T(\ell)>(1-\eta/2)t)$ with $T(\ell)$ a sum of $\ell$ i.i.d. $\tilde G$ lengths → $F^{*\ell}$ for any probability $F$ on $[0,\infty)$ with an exponential moment; reason: $\tilde G$ is such a law (A1 and the previous milestone), so it specializes to the paper's bound
--   - reading: $\psi(\varepsilon)=\varepsilon\lambda^{-1}+o(\varepsilon^2)$ and the bound $\exp(-\varepsilon\eta t/2+\ell o(\varepsilon^2))$ → $\exists\delta>0$ with $F^{*\ell}(((1-\eta/2)t,\infty))\le e^{-\delta t}$ when $m\ell\le(1-\eta)t$; reason: the remainder of $\psi$ is $O(\varepsilon^2)$, not $o(\varepsilon^2)$; with $\varepsilon$ small the printed exponent is at most $-\delta t$, which is how the bound is used
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, Theorem 2, proof, p.287 (PDF p.17), displays bounding P∗(T(ℓ) > (1 − η/2)t)

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open Model

/-- **The Chernoff bound on `T(ℓ)` under `P*`** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004), Theorem 2, proof, p.287), stated for
any cycle law with an exponential moment. Let `F` be a probability measure on `[0, ∞)` with
`∫ e^{ε₀x} F(dx) < ∞` for some `ε₀ > 0`, and mean `m`. Then
1. (Chernoff) for every `ε ⩾ 0`, `ℓ ∈ ℕ` and `x`,
   `F^{*ℓ}((x, ∞)) ⩽ e^{−εx} (∫ e^{εy} F(dy))^ℓ = exp(−εx + ℓψ(ε))`, `ψ(ε) = log ∫ e^{εy} F(dy)`;
2. for every `η ∈ (0, 1)` there is `δ > 0` such that `F^{*ℓ}(((1 − η/2)t, ∞)) ⩽ e^{−δt}` for all
   `t ⩾ 0` and `ℓ ∈ ℕ` with `mℓ ⩽ (1 − η)t`.

**Formalization Note.** The paper applies this to `F = G̃` (mean `λ⁻¹`) and writes the bound as
`exp(−εηt/2 + ℓ o(ε²))` with `ψ(ε) = ελ⁻¹ + o(ε²)`; the remainder is in fact `O(ε²)`, and the
statement gives the resulting exponential bound with an explicit `δ`. -/
theorem chernoff_tail (F : Measure ℝ) [IsProbabilityMeasure F] (hF : F (Set.Iio 0) = 0)
    (hexp : ∃ ε₀ > 0, ∫⁻ x, ENNReal.ofReal (Real.exp (ε₀ * x)) ∂F < ⊤) :
    (∀ ε : ℝ, 0 ≤ ε → ∀ (ℓ : ℕ) (x : ℝ), QueueingFundamentals.MG1.convPow F ℓ (Set.Ioi x) ≤
        ENNReal.ofReal (Real.exp (-ε * x)) * (∫⁻ y, ENNReal.ofReal (Real.exp (ε * y)) ∂F) ^ ℓ) ∧
    ∀ η : ℝ, 0 < η → η < 1 → ∃ δ > 0, ∀ (ℓ : ℕ) (t : ℝ), 0 ≤ t →
      (SmithRegenerative.Equilibrium.mean F).toReal * ℓ ≤ (1 - η) * t →
        QueueingFundamentals.MG1.convPow F ℓ (Set.Ioi ((1 - η / 2) * t)) ≤
          ENNReal.ofReal (Real.exp (-δ * t)) := by sorry

end TabooRegen
