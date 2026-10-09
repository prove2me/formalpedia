-- Prove2me | Theorems.Thm_RegLearnGames_FirstOrder_theorem_23
-- name    : RegLearnGames.FirstOrder.theorem_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:42.597357+00:00
-- url     : https://prove2.me/theorems/bd275669-dd66-4590-98c3-3e96baacd417
-- title:
--   Theorem 23, supp. p. 10 — first-order regret gives fast average-cost convergence in smooth games
-- statement:
--   Consider a finite cost game with $n$ players, $d\ge1$ strategies per player, and costs $c_i(s)\in[0,1]$. Let $C(s)=\sum_i c_i(s)$, let $\mathrm{OPT}'=\min_s C(s)$, and let $C(w)$ be total expected cost under independent mixed play. Suppose the game is $(\lambda,\mu)$-smooth with $0<\mu<1$, and every player satisfies the first-order regret inequality (21) with real constants $A_1,A_2$ over mixed profiles $w^1,\ldots,w^T$, where $T\ge1$. Then
--   $$\frac1T\sum_{t=1}^T C(w^t)\le\frac{\lambda(1+\mu)}{\mu(1-\mu)}\mathrm{OPT}'+\frac{A n\log d}{T},\qquad A=\frac{A_1^2\mu}{(1-\mu)^2}+\frac{2A_2}{1-\mu}.$$
--
--   The result converts each player's small-loss regret guarantee into an average social-cost bound with an additive term that decays as $1/T$.
--
--   **Formalization Note** The paper's divisions require $0<\mu<1$ and $T\ge1$; the strategy set is nonempty so $\mathrm{OPT}'$ is a true minimum and $\log d$ has positive input. The theorem assumes (21) on the realized trajectory, which is supplied by an algorithm guaranteeing it on all sequences. No sign restriction is imposed on $A_1$, $A_2$, or $\lambda$. The sign restriction used in the paper's intermediate Cauchy–Schwarz step applies only to the affected milestones.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, supp. p. 10 (PDF p. 19), Theorem 23

import Mathlib
import Definitions.Def_RegLearnGames_FirstOrder_Setting

namespace RegLearnGames.FirstOrder

open Finset

/-- Theorem 23: first-order regret gives fast convergence in a smooth cost game. -/
theorem theorem_23 {n d : ℕ} [NeZero d]
    (c : Fin n → (Fin n → Fin d) → ℝ)
    (hc : ∀ i s, c i s ∈ Set.Icc (0 : ℝ) 1)
    (lam mu : ℝ) (hmu₀ : 0 < mu) (hmu₁ : mu < 1)
    (hsmooth : IsSmoothCost c lam mu)
    (A₁ A₂ : ℝ)
    (T : ℕ) (hT : 1 ≤ T)
    (w : ℕ → Fin n → Fin d → ℝ)
    (hw : ∀ t ∈ Finset.Icc 1 T, AGT.IsMixedProfile (w t))
    (hreg : HasFirstOrderRegret c w T A₁ A₂) :
    (1 / (T : ℝ)) *
        (∑ t ∈ Finset.Icc 1 T, socialCost c (w t)) ≤
      lam * (1 + mu) / (mu * (1 - mu)) * optCost c +
        (A₁ ^ 2 * mu / (1 - mu) ^ 2 + 2 * A₂ / (1 - mu)) *
          (n : ℝ) * Real.log (d : ℝ) / (T : ℝ) := by sorry

end RegLearnGames.FirstOrder
