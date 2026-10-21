-- Prove2me | Theorems.Thm_ProConChoice_Rational_integral_step
-- name    : ProConChoice.Rational.integral_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:40.829297+00:00
-- url     : https://prove2.me/theorems/7115a1c7-f8d2-4c0c-936d-fe96623c1291
-- title:
--   §7, p. 22 — induction step: a {−1,0,1} weight function representing Cₖ extends to a {−1,0,1} weight function representing Cₖ₊₁
-- statement:
--   Let $X$ be a finite set with $n$ elements, $C$ a choice function on $X$ with associated random choice function $p_C$ ($p_C(x, S) = 1$ if $C(S) = x$ and $0$ otherwise), and $1 \le k \le n - 1$. Suppose $\lambda_k$ is a signed weight function on the $k$-prefixes, with values in $\{-1, 0, 1\}$, that represents $C_k$ (the restriction of $p_C$ to the sets $S$ with $|S| > n - k$). Then there is a signed weight function $\lambda_{k+1}$ on the $(k+1)$-prefixes such that
--
--   1. every value of $\lambda_{k+1}$ is in $\{-1, 0, 1\}$;
--   2. $\lambda_{k+1}$ refines $\lambda_k$ by (14): $\lambda_k([\succ^k]) = \sum \lambda_{k+1}([\succ^{k+1}])$ over the $(k+1)$-prefixes extending $[\succ^k]$;
--   3. $\lambda_{k+1}$ represents $C_{k+1}$.
--
--   Starting from $\lambda_1([\succ_x]) = p_C(x, X) \in \{0, 1\}$ and applying this step up to $k = n$ gives an integer weight function on all orderings that represents $C$, from which the pro-con model of Theorem 1 and Remark 1 is read off.
--
--   **Formalization Note** Weight functions are integer valued, `(Fin k ↪ X) → ℤ`, cast to $\mathbb{R}$ in `Represents` and `Refines`. The hypothesis on $\lambda_k$ is exactly the paper's induction hypothesis (values in $\{-1,0,1\}$ and representation of $C_k$); the paper's argument for this step also uses that the previous step's weights satisfy the bound (33), which it does not establish for the integral vertex it selects, so a proof must either establish this statement in the generality given or reorganize the induction.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 22, Section 7 (proof of Theorem 1), induction hypothesis and step

import Mathlib
import Definitions.Def_ProConChoice_Rational_Model
import Definitions.Def_ProConChoice_Rational_RandomChoice

namespace ProConChoice.Rational

/-- The inductive step of Section 7 (p. 22): for a choice function `C` and `1 ≤ k ≤ n - 1`, if a
signed weight function `λₖ` on `k`-prefixes with values in `{-1, 0, 1}` represents `Cₖ`, then there
is `λₖ₊₁` on `(k+1)`-prefixes with values in `{-1, 0, 1}` that refines `λₖ` by (14) and represents
`Cₖ₊₁`. -/
theorem integral_step {X : Type*} [Fintype X] [DecidableEq X]
    (C : Finset X → X) (hC : IsChoiceFunction C) (k : ℕ) (hk : 1 ≤ k) (hkn : k < Fintype.card X)
    (lam : (Fin k ↪ X) → ℤ) (hlam : ∀ π, lam π = -1 ∨ lam π = 0 ∨ lam π = 1)
    (hrep : Represents k (fun π => (lam π : ℝ)) (choiceRCF C)) :
    ∃ lam' : (Fin (k + 1) ↪ X) → ℤ, (∀ π', lam' π' = -1 ∨ lam' π' = 0 ∨ lam' π' = 1) ∧
      Refines k (fun π => (lam π : ℝ)) (fun π' => (lam' π' : ℝ)) ∧
      Represents (k + 1) (fun π' => (lam' π' : ℝ)) (choiceRCF C) := by sorry

end ProConChoice.Rational
