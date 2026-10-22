-- Prove2me | Theorems.Thm_PersonalizedAssortment_IB_lemma5_ratio_monotone
-- name    : PersonalizedAssortment.IB.lemma5_ratio_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T01:44:57.236693+00:00
-- url     : https://prove2.me/theorems/132d2fe2-0bb7-4a2f-8b77-8bdfc2c13730
-- title:
--   Lemma 5(a): $x\mapsto(1-x)/(2-x-\Psi(x))$ is increasing
-- statement:
--   Let $\Psi$ be a penalty function, i.e. $\Psi:[0,1]\to[0,1]$ increasing with $\Psi(0)=0$ and $\Psi(1)=1$. Suppose that $\Psi$ is also concave and twice differentiable on $[0,1]$. Then the function
--   $$x\;\longmapsto\;\frac{1-x}{2-x-\Psi(x)}$$
--   is (non-strictly) increasing on $[0,1)$.
--
--   This is the first half of Lemma 5. It is used in the second case of the final step of the proof of Theorem 1, where $x>1-1/c_{\min}$.
--
--   **Formalization Note** The paper says "increases on $[0,1]$". At $x=1$ the expression is $0/0$, and Lean would give it the value $0$, which would make the statement false on the closed interval. The domain is therefore $[0,1)$. Twice differentiability is encoded as differentiability of $\Psi$ on $[0,1]$ together with differentiability of its derivative within $[0,1]$.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1548, Lemma 5 (first part)

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction

namespace PersonalizedAssortment.IB

/-- Lemma 5, first part (p. 1548): for an increasing, concave, twice-differentiable penalty function
`Ψ`, the map `x ↦ (1 - x)/(2 - x - Ψ(x))` is increasing (non-strictly). Stated on `[0, 1)`: at
`x = 1` the expression is `0/0`. -/
theorem lemma5_ratio_monotone (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ)
    (hconc : ConcaveOn ℝ (Set.Icc 0 1) Ψ) (hdiff : DifferentiableOn ℝ Ψ (Set.Icc 0 1))
    (hdiff2 : DifferentiableOn ℝ (derivWithin Ψ (Set.Icc 0 1)) (Set.Icc 0 1)) :
    MonotoneOn (fun x : ℝ => (1 - x) / (2 - x - Ψ x)) (Set.Ico 0 1) := by sorry

end PersonalizedAssortment.IB
