-- Prove2me | Theorems.Thm_PersonalizedAssortment_IB_lemma5_tail_antitone
-- name    : PersonalizedAssortment.IB.lemma5_tail_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T01:45:13.797193+00:00
-- url     : https://prove2.me/theorems/791ccd05-0e69-4580-a1ff-cffc3147bc70
-- title:
--   Lemma 5(b): $C\mapsto 1/C+\int_{a+1/C}^1\Psi$ is decreasing on $[1/(1-a),\infty)$
-- statement:
--   Let $\Psi$ be an increasing, concave, twice-differentiable penalty function, with $\Psi:[0,1]\to[0,1]$, $\Psi(0)=0$ and $\Psi(1)=1$. Let $a\in[0,1)$. Then the function
--   $$C\;\longmapsto\;\frac1C+\int_{a+1/C}^{1}\Psi(y)\,dy$$
--   is (non-strictly) decreasing on $[1/(1-a),\infty)$.
--
--   This is the second half of Lemma 5. In the proof of Theorem 1 it lets an inventory level $c_i$ be replaced by the smaller level $c_{\min}$ in the competitive-ratio expression.
--
--   **Formalization Note** The paper allows $a\in[0,1]$. At $a=1$ the interval $[1/(1-a),\infty)$ is undefined, and Lean's convention $1/0=0$ would silently put $C=0$ in the domain, so $a<1$ is required. On the domain, $a+1/C\le1$, so the integral runs over a subinterval of $[0,1]$.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1548, Lemma 5 (second part)

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction

namespace PersonalizedAssortment.IB

/-- Lemma 5, second part (p. 1548): for an increasing, concave, twice-differentiable penalty
function `Ψ` and `a ∈ [0, 1)`, the map `C ↦ 1/C + ∫_{a+1/C}^1 Ψ(y) dy` is decreasing
(non-strictly) on `[1/(1 - a), ∞)`. The paper allows `a = 1`, where `[1/(1 - a), ∞)` is
undefined. -/
theorem lemma5_tail_antitone (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ)
    (hconc : ConcaveOn ℝ (Set.Icc 0 1) Ψ) (hdiff : DifferentiableOn ℝ Ψ (Set.Icc 0 1))
    (hdiff2 : DifferentiableOn ℝ (derivWithin Ψ (Set.Icc 0 1)) (Set.Icc 0 1))
    (a : ℝ) (ha : a ∈ Set.Ico 0 1) :
    AntitoneOn (fun C : ℝ => 1 / C + ∫ y in (a + 1 / C)..1, Ψ y) (Set.Ici (1 / (1 - a))) := by sorry

end PersonalizedAssortment.IB
