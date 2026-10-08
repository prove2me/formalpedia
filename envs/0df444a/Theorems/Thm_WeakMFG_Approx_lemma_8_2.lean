-- Prove2me | Theorems.Thm_WeakMFG_Approx_lemma_8_2
-- name    : WeakMFG.Approx.lemma_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:30:00.13947+00:00
-- url     : https://prove2.me/theorems/ec9b06df-b83c-4248-8af5-e1910efb9d9a
-- title:
--   Lemma 8.2 — $\lim_n\sup_{\beta\in\mathbb A_n}|J_{n,1}(\beta^\alpha)-J'_n(\beta)|=0$
-- statement:
--   In the $n$-player setting of §4, for $\beta\in\mathbb A_n$ let $\beta^\alpha=(\beta,\alpha^2,\dots,\alpha^n)$ and
--   $$J'_n(\beta)=\mathbb E^{P_n(\beta^\alpha)}\Big[\int_0^Tf(t,X^1,\hat\mu,\hat q_t,\beta_t)\,dt+g(X^1,\hat\mu)\Big].$$
--   Then
--   $$\lim_{n\to\infty}\ \sup_{\beta\in\mathbb A_n}\big|J_{n,1}(\beta^\alpha)-J'_n(\beta)\big|=0.$$
--
--   The lemma says that, uniformly over all full-information deviations of player 1, replacing the empirical measures $\mu^n$ and $q^n(\beta^\alpha_t)$ by their mean field limits $\hat\mu$ and $\hat q_t$ changes player 1's value by a vanishing amount.
--
--   **Formalization Note** The supremum is unfolded: for every $\varepsilon>0$ there is $N$ such that for all $n\ge N$ (with $n\ge1$), all $\beta\in\mathbb A_n$ and every version $D$ of $dP_n(\beta^\alpha)/dP$, $|J_{n,1}(\beta^\alpha)-J'_n(\beta)|\le\varepsilon$, both values computed with the same $D$; a version exists. Player 1 is index $0$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), Lemma 8.2, §8.1, pp. 32–33 (J'_n defined on p. 32)

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

/-- Lemma 8.2 (Carmona–Lacker, arXiv:1307.1152v2, §8.1, pp. 32–33):
`lim_{n → ∞} sup_{β ∈ 𝔸_n} |J_{n,1}(β^α) − J′_n(β)| = 0`, where `β^α = (β, α², …, αⁿ)` and
`J′_n(β) = E^{P_n(β^α)}[∫₀ᵀ f(t, X¹, μ̂, q̂_t, β_t) dt + g(X¹, μ̂)]`.
Formalization Note: the supremum is unfolded (for every `ε > 0` there is `N` such that for all
`n ≥ N`, all `β ∈ 𝔸_n` and every version `D` of `dP_n(β^α)/dP` the difference is at most `ε`);
both values use the same version `D`, and a version exists (D6). Player 1 is index `0` (D7). -/
theorem lemma_8_2 (G : Game B Ω' ψ A σ b f g) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ β : ℝ≥0 → Ω' → A,
      G.IsAdmissibleN n β →
        (∃ D, G.IsDensityN n (Function.update (G.αn n) 0 β) D) ∧
        ∀ D, G.IsDensityN n (Function.update (G.αn n) 0 β) D →
          |G.JN n 0 (Function.update (G.αn n) 0 β) D - G.J'N β D| ≤ ε := by sorry

end WeakMFG.Approx
