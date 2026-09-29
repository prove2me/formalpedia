-- Prove2me | Theorems.Thm_PathFindingLP_Centering_centering_with_weights
-- name    : PathFindingLP.Centering.centering_with_weights
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:38:24.001979+00:00
-- url     : https://prove2.me/theorems/ac3454fd-4359-4bf2-b099-51115cb41a93
-- title:
--   Theorem 5 (Centering with Weights, §IV.C): one step contracts $\delta_t$ by $1-\frac{1}{4c_r}$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have full column rank, $b\in\mathbb R^m$, $c\in\mathbb R^n$ and $t\in\mathbb R$. Let $\vec g$ be a weight function for $A$ (Definition 4) with constants $c_1,c_\gamma,c_r$. Let $x^{(old)}\in S^0$, write $s^{(old)}=s(x^{(old)})$, and take the centering step
--   $$x^{(new)}=x^{(old)}-\frac{1}{1+c_r}\,\vec h_t\big(x^{(old)},\vec g(s^{(old)})\big).\qquad(5)$$
--   If
--   $$\delta_t\big(x^{(old)},\vec g(s^{(old)})\big)\le\frac{1}{100\,c_\gamma c_r^2},$$
--   then $x^{(new)}\in S^0$ and, with $s^{(new)}=s(x^{(new)})$,
--   $$\delta_t\big(x^{(new)},\vec g(s^{(new)})\big)\le\Big(1-\frac{1}{4c_r}\Big)\,\delta_t\big(x^{(old)},\vec g(s^{(old)})\big).$$
--
--   Here $\vec h_t$ is the weighted Newton step and $\delta_t$ the centrality of the weighted central path. The theorem says that one step of (5), followed by resetting the weights to the weight function's value at the new slacks, contracts the centrality by a constant factor depending only on $c_r$. Together with Lemma 1 this lets the method double $t$ while staying near the weighted central path in a number of steps governed by $c_\gamma$, $c_r$ and $c_1$.
--
--   **Formalization Note** Full column rank of $A$ is assumed (the paper leaves it implicit; the Newton step and centrality are undefined otherwise). The conclusion $x^{(new)}\in S^0$ is stated explicitly, because the page's conclusion evaluates $\vec g$ at $s^{(new)}$, which is only meaningful for positive slacks. $c_\gamma$ and $c_r$ are the constants of the weight function, and $\vec h=\vec h_t$ with the same $t$; the page places no restriction on $t$, and none is added. This is Theorem 5 of §IV.C, not the Theorem 5 (Centering with Inexact Weights) of §VI.B.
-- source:
--   Lee, Sidford, Path Finding Methods for Linear Programming, FOCS 2014, pp. 424–433, p. 428, §IV.C, Theorem 5 (Centering with Weights), eq. (5)

import Mathlib
import Definitions.Def_PathFindingLP_Centering_WeightFunction

open Matrix

namespace PathFindingLP.Centering

/-- Theorem 5 (Centering with Weights), §IV.C, p. 428: let `g` be a weight function for `A`
with constants `c₁, c_γ, c_r`, let `x_old ∈ S⁰` and
`x_new = x_old - (1/(1+c_r)) h_t(x_old, g(s(x_old)))` (eq. (5)). If
`δ_t(x_old, g(s(x_old))) ≤ 1/(100 c_γ c_r²)` then `x_new ∈ S⁰` and
`δ_t(x_new, g(s(x_new))) ≤ (1 - 1/(4 c_r)) δ_t(x_old, g(s(x_old)))`. -/
theorem centering_with_weights {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n)
    (g : (Fin m → ℝ) → (Fin m → ℝ)) (c₁ cγ cr : ℝ) (hg : IsWeightFunction A g c₁ cγ cr)
    (t : ℝ) (xOld : Fin n → ℝ) (hx : xOld ∈ interiorS0 A b)
    (hδ : centrality A b c t xOld (g (slack A b xOld)) ≤ 1 / (100 * cγ * cr ^ 2)) :
    let xNew := xOld - (1 / (1 + cr)) • newtonStep A b c t xOld (g (slack A b xOld))
    xNew ∈ interiorS0 A b ∧
      centrality A b c t xNew (g (slack A b xNew)) ≤
        (1 - 1 / (4 * cr)) * centrality A b c t xOld (g (slack A b xOld)) := by sorry

end PathFindingLP.Centering
