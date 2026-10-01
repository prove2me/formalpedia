-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_weak_duality
-- name    : SteinitzExchange.Duality.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:56:01.350367+00:00
-- url     : https://prove2.me/theorems/be74cf38-77f7-485d-a427-d577810f3279
-- title:
--   Lemma 6.3 — weak duality and the Fenchel identity (6.5) for arbitrary functions on finite sets
-- statement:
--   Let $B_1,B_2\subseteq\mathbb Z^V$ be finite nonempty sets (no exchange axiom is assumed), and let $\omega:B_1\to\mathbb R$, $\zeta:B_2\to\mathbb R$ be arbitrary. With the conjugates $\omega^\circ,\zeta^\bullet$ and the closures $\hat\omega,\check\zeta$ taken with respect to $B_1$ and $B_2$ respectively,
--
--   $$\max\{\omega(x)-\zeta(x)\mid x\in B_1\cap B_2\}\;\le\;\max\{\hat\omega(b)-\check\zeta(b)\mid b\in\overline{B_1}\cap\overline{B_2}\}\;=\;\inf\{\zeta^\bullet(p)-\omega^\circ(p)\mid p\in\mathbb R^V\},$$
--
--   where a maximum over an empty family is $-\infty$ and the infimum may be $-\infty$. When $\overline{B_1}\cap\overline{B_2}\neq\emptyset$, the middle maximum is attained.
--
--   The equality is the Fenchel duality (6.5) for the polyhedral concave function $\hat\omega$ and polyhedral convex function $\check\zeta$; it holds with no constraint qualification. The inequality is the weak half of the min-max theorem of the mission.
--
--   **Formalization Note.** All three values are in `EReal` (`primalValue`, `relaxedValue`, `dualValue`). "Max" is rendered as a supremum together with an explicit attainment clause for the relaxed problem; the primal maximum is over a finite set.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 295, Lemma 6.3 (and Eq. (6.5), pp. 294-295)

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Conjugate
import Definitions.Def_SteinitzExchange_Duality_Problems

namespace SteinitzExchange.Duality

/-- Murota 1996, p. 295, Lemma 6.3 (weak duality, with the Fenchel identity (6.5)): for any
functions `ω : B₁ → ℝ` and `ζ : B₂ → ℝ` on nonempty finite sets `B₁, B₂ ⊆ ℤ^V` (no (B1) needed),
`max{ω(x) − ζ(x) | x ∈ B₁ ∩ B₂} ≤ max{ω̂(b) − ζ̌(b) | b ∈ B̄₁ ∩ B̄₂}
  = inf{ζ•(p) − ω°(p) | p ∈ ℝ^V}`,
all values in `EReal` with `max ∅ = −∞`; the relaxed maximum is attained when `B̄₁ ∩ B̄₂ ≠ ∅`. -/
theorem weak_duality {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (ω ζ : (V → ℤ) → ℝ) :
    primalValue B₁ B₂ ω ζ ≤ relaxedValue B₁ B₂ ω ζ ∧
    relaxedValue B₁ B₂ ω ζ = dualValue B₁ B₂ ω ζ ∧
    ((hull B₁ ∩ hull B₂).Nonempty →
      ∃ b ∈ hull B₁ ∩ hull B₂,
        relaxedValue B₁ B₂ ω ζ = ((concaveClosure B₁ ω b - convexClosure B₂ ζ b : ℝ) : EReal)) := by sorry

end SteinitzExchange.Duality
