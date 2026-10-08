-- Prove2me | Theorems.Thm_SennottDP_BOR_limitFunction_le_passage
-- name    : SennottDP.BOR.limitFunction_le_passage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T11:29:46.046991+00:00
-- url     : https://prove2.me/theorems/6ab031e2-8575-45e4-9357-2386789ce443
-- title:
--   Lemma 7.4.2 — $h(i)\le c_{iG}(\theta)-Jm_{iG}(\theta)+E_\theta[h(X_T)]$
-- statement:
--   Assume the (SEN) assumptions hold for $z$, with $M$ the function of (SEN2) and $L$ the constant of (SEN3), and let $J=\lim_{\alpha\to1^-}(1-\alpha)V_\alpha(i)$ be the finite constant of Theorem 7.2.3(i). Let $i$ be a state, $G$ a nonempty set of states and $\theta\in\Re(i,G)$ a policy with
--   $$
--   \sum_{j\in G}M(j)P_\theta(X_T=j)<\infty,
--   $$
--   where $T$ is the first passage time from $i$ to $G$. Then for every limit function $h$,
--   $$
--   h(i)\le c_{iG}(\theta)-J\,m_{iG}(\theta)+E_\theta[h(X_T)\mid X_0=i],\qquad(7.23)
--   $$
--   where $E_\theta[h(X_T)\mid X_0=i]=\sum_jh(j)P_\theta(X_T=j)$ is an absolutely convergent series. If $\theta\notin\Re^*(i,G)$ the right side is $+\infty$.
--
--   This upper bound on limit functions is the tool behind the sufficient conditions for the ACOE in Theorem 7.4.3.
--
--   **Formalization Note** The inequality is stated in the extended reals with $c_{iG}(\theta)\in[0,\infty]$, so it reads $h(i)\le+\infty$ when $c_{iG}(\theta)=\infty$; $m_{iG}(\theta)$ is finite because $\theta\in\Re(i,G)$. The absolute convergence of $\sum_jh(j)P_\theta(X_T=j)$ is stated as part of the conclusion, so the real series is not a default value.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 140, Lemma 7.4.2, (7.23)

import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Lemma 7.4.2, p. 140. Assume (SEN) holds for `z` with the function `Mf` of
(SEN2) and the constant `L` of (SEN3), and let `J = lim_{α→1⁻} (1−α)V_α(i)` be the constant of
Theorem 7.2.3(i). Let `i` be a state, `G` a nonempty set and `θ ∈ ℜ(i,G)` a policy with
`∑_{j∈G} Mf(j) P_θ(X_T = j) < ∞`, where `T` is the first passage time from `i` to `G`. Then for
every limit function `h`, `E_θ[h(X_T) | X_0 = i] = ∑_j h(j) P_θ(X_T = j)` converges absolutely and
`h(i) ≤ c_{iG}(θ) − J m_{iG}(θ) + E_θ[h(X_T) | X_0 = i]` (7.23), the right side being `+∞` when
`c_{iG}(θ) = ∞`. -/
theorem limitFunction_le_passage {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (Mf : S → ℝ) (L : ℝ) (hSEN : SENWith M z Mf L) (J : ℝ) (hJ0 : 0 ≤ J)
    (hJ : ∀ i, Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * valueFn M α i) (𝓝[<] 1)
      (𝓝 (ENNReal.ofReal J)))
    (h : S → ℝ) (hh : IsLimitFunction M z h) (i : S) (G : Set S) (hG : G.Nonempty)
    (θ : SennottDP.Discounted.Policy M) (hθ : InR θ i G)
    (hMG : ∑' j : G, ENNReal.ofReal (Mf j) * hitDist θ i G j < ⊤) :
    Summable (fun j => h j * (hitDist θ i G j).toReal) ∧
    (h i : EReal) ≤ ((passageCost θ i G : ℝ≥0∞) : EReal) - ((J * (meanPassage θ i G).toReal : ℝ) : EReal)
      + ((∑' j, h j * (hitDist θ i G j).toReal : ℝ) : EReal) := by sorry

end SennottDP.BOR
