-- Prove2me | Theorems.Thm_TimeVaryingGames_lemma_1
-- name    : TimeVaryingGames.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:07.470384+00:00
-- url     : https://prove2.me/theorems/dc34549a-b521-4003-b5e5-41ff3a99ca43
-- title:
--   Lemma 1, p.15: $\lambda_{ij}=\lambda_i/\lambda_j$
-- statement:
--   Let $\gamma_{i,t}>0$ be step sizes of a finite nonempty set of players satisfying
--   $$\sum_{t}\gamma_{i,t}=\infty\ \text{for all }i\quad\text{(S1)},\qquad \sum_t|\gamma_{i,t}-\lambda_{ij}\gamma_{j,t}|<\infty\ \text{for all }i,j\quad\text{(S2)},$$
--   with constants $\lambda_{ij}>0$, and let $\lambda_i=(\prod_{j}\lambda_{ij})^{1/N}$. Then
--   $$\lambda_{ij}=\frac{\lambda_i}{\lambda_j}\qquad\text{for all }i,j.$$
--
--   The lemma shows that compatible step sizes run on clocks with well-defined relative speeds $\lambda_i$, so that (S2) can be rewritten as $\sum_t|\gamma_{i,t}/\lambda_i-\gamma_{j,t}/\lambda_j|<\infty$.
--
--   Differences from the source:
--   - generalization: γ_{i,t} non-increasing, assumed throughout (p.7, item 4) → no monotonicity of γ i is assumed; only 0 < γ i t; reason: the argument of (35)–(37) never uses monotonicity of the step sizes; non-increasing step sizes are an instance
--   - encoding: stages t = 1, 2, … → t : ℕ starting at 0 (Lean's t is stage t + 1); reason: index shift; same sequences
--   - encoding: (S2) holds for some λ_ij > 0 → a family lam : ι → ι → ℝ with lam i j > 0 as a parameter; reason: choosing the witnesses of the existential once for all pairs
--   - encoding: Σ_t γ_{i,t} = ∞ for positive γ_{i,t} → ¬ Summable (γ i); reason: for positive terms, non-summability is divergence to +∞
--   - encoding: N = {1, …, N} players, compact convex K_i → Nonempty ι (and, where existence matters, nonempty K_i); reason: nondegeneracy implicit in the paper: a game has a player and every player has an action
--   - encoding: Σ_t a_t < ∞ for the nonnegative series of (S2), (S3) → Summable; reason: for nonnegative terms, a finite sum is summability
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, Lemma 1, p.15, with (S1), (S2), p.10, and (34), p.15

import Mathlib
import Definitions.Def_TimeVaryingGames_Weights

namespace TimeVaryingGames

/-- **Lemma 1 (decomposition of the compatibility weights).**
arXiv:1809.03066v3, §4.3, p.15: "Lemma 1. Suppose that γ_{i,t} satisfies (S1) and (S2). Then
λ_{ij} = λ_i/λ_j for all i, j ∈ N." Here (S1) (p.10) is "Σ_{t=1}^∞ γ_{i,t} = ∞ for all i ∈ N",
(S2) (p.10) is "Σ_{t=1}^∞ |γ_{i,t} − λ_{ij}γ_{j,t}| < ∞ for some λ_{ij} > 0" for every pair
`i, j`, the step sizes are positive (p.7), and `λ_i = (∏_j λ_{ij})^{1/N}` is (34).

**Formalization Note.** The constants `λ_{ij}` of (S2) are the parameter `lam`; `speed lam i` is
`λ_i`. For a sequence of positive terms, `¬ Summable` is divergence of the series to `+∞`. -/
theorem lemma_1 {ι : Type*} [Fintype ι] [Nonempty ι] (γ : ι → ℕ → ℝ)
    (hγ : ∀ i t, 0 < γ i t) (hS1 : ∀ i, ¬ Summable (γ i))
    (lam : ι → ι → ℝ) (hlam : ∀ i j, 0 < lam i j)
    (hS2 : ∀ i j, Summable fun t => |γ i t - lam i j * γ j t|) :
    ∀ i j, lam i j = speed lam i / speed lam j := by sorry

end TimeVaryingGames
