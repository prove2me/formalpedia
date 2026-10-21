-- Prove2me | Theorems.Thm_ServTimeLimit_OptMech_lambda1_foc
-- name    : ServTimeLimit.OptMech.lambda1_foc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:42.158296+00:00
-- url     : https://prove2.me/theorems/d4df7ade-2126-4893-9cd0-d69128039755
-- title:
--   Proof of Theorem 1, p. 39 — without a time limit, ∂SW/∂θl vanishes at θl = θ̄/4 exactly when Λ = Λ1
-- statement:
--   Assume $\Lambda, c, \bar\theta > 0$ and $\Lambda < 32/(15\bar\theta)$. For $x \in \mathbb R$ let $SW(x)$ be the social welfare of the allocation that admits $[x, \bar\theta]$ and gives every admitted customer her full need, $t(\theta) = \theta$. Then
--   $$SW'(\bar\theta/4) = 0 \iff \Lambda = \Lambda_1 = \frac{32\left(4c+5-\sqrt{2c(8c+7)}\right)}{3(26c+25)}\cdot\frac1{\bar\theta},$$
--   where the left side means that $SW$ is differentiable at $\bar\theta/4$ with derivative $0$.
--
--   This is the defining property of $\Lambda_1$: it is the arrival rate at which the first-best lower threshold without a time limit equals $\bar\theta/4$, the point beyond which a time limit becomes optimal.
--
--   **Formalization Note** The page writes $\partial\pi/\partial\theta_l$ for what is the derivative of social welfare (the first best has no revenue); the statement is for welfare. The hypothesis $\Lambda < 32/(15\bar\theta)$ is added: at $\theta_l = \bar\theta/4$ the load is $\Lambda \cdot 15\bar\theta^2/32$, so this is exactly the range where the waiting time at $\bar\theta/4$ is defined. The first-order equation has a second root, $32(4c+5+\sqrt{2c(8c+7)})/(3(26c+25)\bar\theta)$, which exceeds $32/(15\bar\theta)$ for every $c > 0$. The derivative is stated with `HasDerivAt`, so that a non-differentiable point does not count as a zero.
-- source:
--   Feldman & Segev, The Important Role of Time Limits when Consumers Choose their Time in Service, SSRN 3424317 (version of 2021-10-07), p. 39, proof of Theorem 1, definition of Λ1

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

namespace ServTimeLimit.OptMech

open MeasureTheory

/-- The `Λ₁` first-order condition (proof of Theorem 1, p. 39): without a time limit
(admitted set `[θ_l, θ̄]`, `t(θ) = θ`), the derivative of social welfare in `θ_l` vanishes at
`θ_l = θ̄/4` exactly when `Λ = Λ₁`, on the range `Λ < 32/(15 θ̄)` where the queue with
`θ_l = θ̄/4` is stable. -/
theorem lambda1_foc (P : Params) (hP : P.Standing) (hstab : P.Lam < 32 / (15 * P.θbar)) :
    HasDerivAt (fun x : ℝ => welfare P (Set.Icc x P.θbar) (fun θ => θ)) 0 (P.θbar / 4) ↔
      P.Lam = lam1 P := by sorry

end ServTimeLimit.OptMech
