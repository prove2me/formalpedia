-- Prove2me | Theorems.Thm_WeakMFG_Approx_density_Lp_bound
-- name    : WeakMFG.Approx.density_Lp_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:57.994883+00:00
-- url     : https://prove2.me/theorems/c229730a-acfa-4f8e-afb7-4943b93bba79
-- title:
--   §8.1, proof of Lemma 8.2 — the densities $dP_n(\beta^\alpha)/dP$ are bounded in $L^p$, uniformly in $n$ and $\beta$
-- statement:
--   In the $n$-player setting of §4, for $\beta\in\mathbb A_n$ let $\beta^\alpha=(\beta,\alpha^2,\dots,\alpha^n)$ be the profile in which player 1 deviates to $\beta$ and the others keep their distributed controls. Then for every $p\ge1$ there is a finite constant $C_p$ with
--   $$\mathbb E\Big[\Big(\frac{dP_n(\beta^\alpha)}{dP}\Big)^p\Big]\le C_p\qquad\text{for all }n\ge1\text{ and }\beta\in\mathbb A_n,$$
--   that is, $\{dP_n(\beta^\alpha)/dP:\beta\in\mathbb A_n,\ n\ge1\}$ is bounded in $L^p(P)$.
--
--   The bound is used, with Hölder's inequality, to pass from expectations under $P$ to expectations under the deviation measures $P_n(\beta^\alpha)$ uniformly in the deviation.
--
--   **Formalization Note** The density is a relation over versions of the Itô integrals: the bound holds for every version, and a version exists for every $n$ and $\beta$. Player 1 is index $0$. The constant is a finite nonnegative real, independent of $n$ and $\beta$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §8.1, proof of Lemma 8.2, p. 33, first paragraph

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

/-- §8.1, proof of Lemma 8.2 (Carmona–Lacker, arXiv:1307.1152v2, p. 33): "Similar to the proof of
Lemma 7.7, `{dP_n(β^α)/dP : β ∈ 𝔸_n, n ≥ 1}` are bounded in `L^p(P)`, for any `p ≥ 1`", where
`β^α = (β, α², …, αⁿ)` (player 1 deviates; index `0`, D7). For every `p ≥ 1` there is a finite `C`
with `E[(dP_n(β^α)/dP)^p] ≤ C` for all `n ≥ 1`, `β ∈ 𝔸_n` and all versions of the density, and a
version exists (D6). -/
theorem density_Lp_bound (G : Game B Ω' ψ A σ b f g) :
    ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ≥0, ∀ (n : ℕ) [NeZero n] (β : ℝ≥0 → Ω' → A),
      G.IsAdmissibleN n β →
        (∃ D, G.IsDensityN n (Function.update (G.αn n) 0 β) D) ∧
        ∀ D, G.IsDensityN n (Function.update (G.αn n) 0 β) D →
          ∫⁻ ω, ‖D ω‖ₑ ^ p ∂G.P' ≤ (C : ℝ≥0∞) := by sorry

end WeakMFG.Approx
