-- Prove2me | Theorems.Thm_RobustCtxPricing_lemma_3_5
-- name    : RobustCtxPricing.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:59:29.077313+00:00
-- url     : https://prove2.me/theorems/cae47cc5-840b-427a-b0fd-a8d8eb2fe87e
-- title:
--   Lemma 3.5 — at most $4C+20d\log T$ density-update rounds with a far median
-- statement:
--   Let $d\ge1$, $T,C\in\mathbb N$, $\epsilon=T^{-3}$, $\theta^\star\in\Theta$ and contexts $u_1,\dots,u_T\in\Theta$. Consider a density process: $\mu_1$ is the uniform density over $\Theta$, and in each round $t$ either the density is kept ($\mu_{t+1}=\mu_t$), or $t$ is an *update round*: the posted price $m_t$ is an $\epsilon$-window median of $\mu_t$ in direction $u_t$ and $\mu_{t+1}=$ Update-Density$(\mu_t,u_t,m_t,Y_t)$. Suppose that, outside a set $S$ of at most $C$ rounds, the feedback of every update round is the true sale bit, $Y_t=\mathbb I\{m_t\le\langle\theta^\star,u_t\rangle\}$. Then the number of update rounds with $x_t=0$, that is with $|m_t-\langle\theta^\star,u_t\rangle|>\epsilon$, is at most
--   $$
--   4C+20\,d\log T .
--   $$
--   This bounds the exploration rounds in which the median is far from the valuation, both for Algorithm 1 and for Algorithm 4, where every exploration round updates the density.
--
--   Differences from the source:
--   - generalization: the update rounds of Algorithm 1 or Algorithm 4 → an arbitrary density process (any set of update rounds, any window medians, any contexts in Θ, any feedback); reason: both algorithms' density trajectories are instances
--   - generalization: Y_t = y_t for every t ∉ S → Y_t = y_t only for update rounds t ∉ S, with S any set of at most C natural numbers; reason: a weaker hypothesis; the feedback of the other rounds is never read, and rounds of S outside [T] change nothing
--   - generalization: the model's standing assumption v_t = ⟨θ⋆, u_t⟩ ≥ 0 → not assumed; reason: the statement holds without it and specializes to the model
--   - encoding: a set 𝒯 ⊆ [T] of update rounds and x_t = 0 → the count over all update rounds of |m_t − ⟨θ⋆, u_t⟩| > ϵ; reason: x_t = 𝕀{|p_t − v_t| ≤ ϵ} with p_t = m_t; counting all update rounds bounds the count over every subset 𝒯
--   - reading: 𝓑_d(0,1), "the d-dimensional Euclidean ball" → the closed unit ball; reason: the analysis uses ‖u_t‖₂ ≤ 1 and ‖θ⋆‖₂ ≤ 1 (pp.18, 21); the closed ball contains the open one and differs from it by a null set
--   - encoding: the dimension d ∈ ℕ of ℝ^d → a natural number d with 1 ≤ d; reason: the context dimension of the model; d = 0 has no directions and is not an instance of it
--   - reading: the budget C, an upper bound on the number of corrupted rounds (its type is not stated) → C ∈ ℕ; reason: it bounds the count |S|
--   - reading: log → the natural logarithm Real.log; reason: the base is not stated; natural log is the standard meaning, and the constants of p.17 hold with it
--   - encoding: rounds t = 1, …, T and bits in {0, 1} → rounds 0, …, T − 1 of ℕ-indexed sequences and Bool bits; reason: Lean convention; same instances
--   - encoding: the cases of Update-Density overlap on the hyperplanes ⟨u_t, θ⟩ = m_t ± ϵ/2 → the window case takes priority there; reason: the page leaves the overlap open; for u_t ≠ 0 the hyperplanes are null, and for u_t = 0 a window median of a positive mass has |m_t| < ϵ/2, so they do not meet the update
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, Lemma 3.5, p.16 (x_t defined on p.12)

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Density
import Definitions.Def_RobustCtxPricing_Algorithm4

namespace RobustCtxPricing

/-- **Lemma 3.5.** Castiglioni–Stradi, *Decoupling Corruption and Horizon in Robust Contextual
Pricing*, arXiv:2607.11210, §3.2.2, p.16: "Let `𝒯 ⊆ [T]` denote a set of rounds in which the
Update-Density procedure is invoked; this might include rounds in which `X_t = 1`. Then, the number
of rounds `t ∈ 𝒯` such that `x_t = 0` is at most `4C + 20d log T`."

Abstract density process: `μ_1` is the uniform density over `Θ`; in each round `t < T` either the
density is kept (`t ∉ 𝒯`), or (`t ∈ 𝒯`) the posted price `m_t` is an ϵ-window median of `μ_t` in
direction `u_t` and `μ_{t+1}` = Update-Density(`μ_t, u_t, m_t, Y_t`), with `ϵ = T⁻³`. The feedback
`Y_t` equals the true sale bit `𝕀{m_t ≤ ⟨θ⋆, u_t⟩}` in every update round outside a set `S` of at
most `C` rounds. Then the number of update rounds with `x_t = 0`, i.e. `|m_t − ⟨θ⋆, u_t⟩| > ϵ`, is at
most `4C + 20 d log T`.

**Formalization Note.** The abstract process covers Algorithm 1 (update when `X_t = 0`) and
Algorithm 4 (update in every exploration round) at once. `x_t = 𝕀{|p_t − v_t| ≤ ϵ}` (p.12) with
`p_t = m_t`. Contexts lie in `Θ`. Rounds are `0, …, T−1`; `log` is natural. -/
theorem lemma_3_5 (d T C : ℕ) (hd : 1 ≤ d) (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ Theta d)
    (u : ℕ → EuclideanSpace ℝ (Fin d)) (hu : ∀ t < T, u t ∈ Theta d)
    (μ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (m : ℕ → ℝ) (Y : ℕ → Bool) (upd : Finset ℕ)
    (h0 : μ 0 = uniformDensity d)
    (hstep : ∀ t < T,
      (t ∈ upd ∧ IsWindowMedian (epsT T) (μ t) (u t) (m t) ∧
        μ (t + 1) = updateDensity (epsT T) (μ t) (u t) (m t) (Y t)) ∨
      (t ∉ upd ∧ μ (t + 1) = μ t))
    (S : Finset ℕ) (hS : S.card ≤ C)
    (hY : ∀ t < T, t ∈ upd → t ∉ S → Y t = decide (m t ≤ inner ℝ θ (u t))) :
    (((Finset.range T).filter
        (fun t => t ∈ upd ∧ epsT T < |m t - inner ℝ θ (u t)|)).card : ℝ) ≤
      4 * C + 20 * d * Real.log T := by sorry

end RobustCtxPricing
