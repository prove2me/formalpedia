-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_Supplement_supConv_exc
-- name    : SteinitzExchange.Duality.Supplement.supConv_exc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:29:02.864316+00:00
-- url     : https://prove2.me/theorems/8e7612aa-ff11-4fb2-95c8-9cc2c479a0dc
-- title:
--   Theorem 6.10 — the supremum convolution of M-concave functions is M-concave
-- statement:
--   Let $V$ be a finite nonempty set and $B_1,B_2\subseteq\mathbb Z^V$ finite integral base sets (finite nonempty sets satisfying the exchange axiom (B1)). Let $\omega_1:B_1\to\mathbb R$ and $\omega_2:B_2\to\mathbb R$ satisfy the exchange property (EXC). Then their supremum convolution
--   $$(\omega_1\,\square\,\omega_2)(x)=\max\{\omega_1(x_1)+\omega_2(x_2)\mid x_1+x_2=x,\ x_1\in B_1,\ x_2\in B_2\}\qquad(x\in B_1+B_2)$$
--   satisfies (EXC) on the Minkowski sum $B_1+B_2=\{x_1+x_2\mid x_1\in B_1,x_2\in B_2\}$.
--
--   Recall that $\omega:B\to\mathbb R$ satisfies (EXC) if for $x,y\in B$ and $u\in\operatorname{supp}^+(x-y)$ there is $v\in\operatorname{supp}^-(x-y)$ with $x-\chi_u+\chi_v\in B$, $y+\chi_u-\chi_v\in B$ and $\omega(x)+\omega(y)\le\omega(x-\chi_u+\chi_v)+\omega(y+\chi_u-\chi_v)$.
--
--   This makes the M-concave functions closed under convolution; as a consequence the union of two valuated matroids carries a valuation (Theorem 7.4).
--
--   **Formalization Note.** `minkSum B₁ B₂` is $B_1+B_2$ and `supConv B₁ ω₁ B₂ ω₂` is $\omega_1\,\square\,\omega_2$ (a maximum on $B_1+B_2$). (EXC) is the published `SatisfiesEXC`.
--
--   Differences from the source: none.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 303, Theorem 6.10

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Definitions.Def_SteinitzExchange_Duality_Supplement_Convolution

namespace SteinitzExchange.Duality.Supplement

/-- Murota 1996, p. 303, Theorem 6.10. Let `B₁, B₂ ⊆ ℤ^V` be finite integral base sets. If
`ω₁ : B₁ → ℝ` and `ω₂ : B₂ → ℝ` satisfy (EXC), then the supremum convolution
`ω₁ □ ω₂ : B₁ + B₂ → ℝ` satisfies (EXC). -/
theorem supConv_exc {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (ω₁ ω₂ : (V → ℤ) → ℝ) (hω₁ : SatisfiesEXC B₁ ω₁) (hω₂ : SatisfiesEXC B₂ ω₂) :
    SatisfiesEXC (minkSum B₁ B₂) (supConv B₁ ω₁ B₂ ω₂) := by sorry

end SteinitzExchange.Duality.Supplement
