-- Prove2me | Theorems.Thm_WeakMFG_Approx_lemma_8_1
-- name    : WeakMFG.Approx.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:29:02.90962+00:00
-- url     : https://prove2.me/theorems/8f042dbe-97bf-466a-a08b-e7fe39379257
-- title:
--   Lemma 8.1 — $\mathbb E|F(X^i,\mu^n)-F(X^i,\hat\mu)|^p\to0$ for $p\in[1,2)$
-- statement:
--   Work in the $n$-player setting of §4, where the states $X^1,X^2,\dots$ are i.i.d. with common law $\hat\mu$ and $\mu^n=\frac1n\sum_{j=1}^n\delta_{X^j}$. Let $F:\mathcal C\times\mathcal P_\psi(\mathcal C)\to\mathbb R$ be empirically measurable, suppose $F(x,\cdot)$ is $\tau_\psi(\mathcal C)$-continuous at $\hat\mu$ for each $x\in\mathcal C$, and suppose there is $c>0$ with
--   $$|F(x,\mu)|\le c\Big(\psi(x)+\int\psi\,d\mu\Big)\quad\text{for all }(x,\mu)\in\mathcal C\times\mathcal P_\psi(\mathcal C).$$
--   Then, for each $i$ and each $p\in[1,2)$,
--   $$\lim_{n\to\infty}\mathbb E\big[|F(X^i,\mu^n)-F(X^i,\hat\mu)|^p\big]=0.$$
--
--   This law of large numbers in the topology $\tau_\psi$ is what lets the empirical measure $\mu^n$ be replaced by $\hat\mu$ in the rewards of the $n$-player game.
--
--   **Formalization Note** The statement is posed inside the full setting of §4 (no extra hypotheses: that the $X^i$ are i.i.d. with law $\hat\mu$ is a consequence of the setting, as the paper recalls). Players are indexed from $0$; the $n$-th term of the sequence uses the first $n+1$ states. The expectation is a lower Lebesgue integral in $[0,\infty]$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), Lemma 8.1, §8.1, p. 32

import Mathlib
import Definitions.Def_WeakMFG_Approx_Game

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace WeakMFG.Approx

variable {d : ℕ} {T : ℝ≥0} {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [MeasurableSpace EA] [BorelSpace EA] {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {B : Base d Ω} {ψ : WeakMFG.Existence.Path d T → ℝ} {A : Set EA}
  {σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ}
  {b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ)}
  {f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ} {g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ}

/-- Lemma 8.1 (Carmona–Lacker, arXiv:1307.1152v2, §8.1, p. 32), in the setting of §4 (`Game`).
Let `F : C × P_ψ(C) → ℝ` be empirically measurable (Definition 3.1), with `F(x, ·)`
`τ_ψ(C)`-continuous at `μ̂` for each `x ∈ C`, and `|F(x, μ)| ≤ c (ψ(x) + ∫ ψ dμ)` for some `c > 0`.
Then `lim_{n → ∞} E[|F(Xⁱ, μⁿ) − F(Xⁱ, μ̂)|^p] = 0` for each `i` and `p ∈ [1, 2)`.
Formalization Note: players are indexed from `0` (D7); the sequence index `n` stands for the
empirical measure of the first `n + 1` states; the expectation is a lower Lebesgue integral in
`ℝ≥0∞` (no junk value for non-integrable integrands). -/
theorem lemma_8_1 (G : Game B Ω' ψ A σ b f g) (F : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (hF_emp : ∀ (n : ℕ) [NeZero n],
      Measurable (fun p : WeakMFG.Existence.Path d T × (Fin n → WeakMFG.Existence.Path d T) => F p.1 (empPath p.2)))
    (hF_cont : ∀ x, ContinuousAt (F x) G.μh)
    (hF_growth : ∃ c > (0 : ℝ), ∀ x (μ : Ppsi ψ), |F x μ| ≤ c * (ψ x + ∫ y, ψ y ∂μ.μ)) :
    ∀ (i : ℕ) (p : ℝ), 1 ≤ p → p < 2 →
      Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal
          (|F (G.Xpn i ω) (G.empN (n + 1) ω) - F (G.Xpn i ω) G.μh| ^ p) ∂G.P')
        atTop (𝓝 0) := by sorry

end WeakMFG.Approx
