-- Prove2me | Theorems.Thm_WeakMFG_Approx_lemma_8_3
-- name    : WeakMFG.Approx.lemma_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:53.498144+00:00
-- url     : https://prove2.me/theorems/0d951130-f1e3-4e62-a3b0-9e2c40b5902c
-- title:
--   Lemma 8.3 — $J'_n(\alpha^1)\ge J'_n(\beta)$ for every $\beta\in\mathbb A_n$
-- statement:
--   In the $n$-player setting of §4, with $J'_n$ as in Lemma 8.2, for every $n\ge1$ and every $\beta\in\mathbb A_n$,
--   $$J'_n(\alpha^1)\ \ge\ J'_n(\beta).$$
--   Here $J'_n(\alpha^1)$ is computed under $P_n((\alpha^1)^\alpha)=P_n(\alpha)$, which is $P$ itself.
--
--   Thus, once the empirical measures are replaced by the mean field equilibrium $(\hat\mu,\hat q)$, no full-information deviation of player 1 improves on the distributed control $\alpha^1$: the optimality of $\hat\alpha$ in the mean field problem survives the enlargement of the information to $\mathbb F^n$.
--
--   **Formalization Note** The inequality holds for all versions of the two densities, and versions exist. Player 1 is index $0$; $J'_n(\alpha^1)$ is evaluated with a version of the density of the undeviated profile $(\alpha^1,\dots,\alpha^n)$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), Lemma 8.3, §8.1, p. 33

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

/-- Lemma 8.3 (Carmona–Lacker, arXiv:1307.1152v2, §8.1, p. 33): for any `β ∈ 𝔸_n`,
`J′_n(α¹) ≥ J′_n(β)`. Here `J′_n(β)` is computed under `P_n(β^α)` and `J′_n(α¹)` under
`P_n((α¹)^α) = P_n(α)`; the inequality holds for all versions of the two densities, and versions
exist (D6). Player 1 is index `0` (D7). -/
theorem lemma_8_3 (G : Game B Ω' ψ A σ b f g) :
    ∀ (n : ℕ) [NeZero n] (β : ℝ≥0 → Ω' → A), G.IsAdmissibleN n β →
      (∃ D, G.IsDensityN n (Function.update (G.αn n) 0 β) D) ∧
      (∃ D, G.IsDensityN n (G.αn n) D) ∧
      ∀ Dβ Dα, G.IsDensityN n (Function.update (G.αn n) 0 β) Dβ → G.IsDensityN n (G.αn n) Dα →
        G.J'N β Dβ ≤ G.J'N (G.αn n 0) Dα := by sorry

end WeakMFG.Approx
