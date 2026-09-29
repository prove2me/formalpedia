-- Prove2me | Theorems.Thm_RobustGeneralization_BernUpper_threshold_undoes_linf_adversary
-- name    : RobustGeneralization.BernUpper.threshold_undoes_linf_adversary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:32:01.589447+00:00
-- url     : https://prove2.me/theorems/2192a4bc-f78a-4c27-add7-116ae0a09d72
-- title:
--   §2.2, p. 7 — thresholding undoes every ℓ∞ adversary: T(B∞^ε(x)) = {x} for x ∈ {±1}^d, 0 ≤ ε < 1
-- statement:
--   Let $T:\mathbb R^d\to\mathbb R^d$ be the thresholding map $T(x)_i=+1$ if $x_i\ge0$ and $-1$ otherwise, and let $\mathcal B^\varepsilon_\infty(x)=\{x'\in\mathbb R^d:\|x'-x\|_\infty\le\varepsilon\}$. For every $x\in\{\pm1\}^d$ and every $0\le\varepsilon<1$,
--   $$T\big(\mathcal B^\varepsilon_\infty(x)\big)=\{x\}.$$
--
--   Every $\ell_\infty$-perturbation of size less than $1$ of a hypercube point is mapped back to that point, so a classifier composed with $T$ has the same robust and standard error on the Bernoulli model. This is what makes a small robust error attainable with one sample.
--
--   **Formalization Note.** The hypothesis $\varepsilon\ge0$ is added: for $\varepsilon<0$ the ball is empty and its image is $\emptyset\neq\{x\}$. The ball is the $\ell_\infty$ ball, written coordinatewise.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, §2.2, p. 7, the sentence after the definition of T

import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

/-- Schmidt et al., arXiv:1804.11285v2, §2.2, p. 7, the sentence after the definition of `T`:
for `ε < 1` the thresholding operator undoes any ℓ∞-bounded adversary, `T(B∞^ε(x)) = {x}` for
every `x ∈ {±1}^d`. The hypothesis `0 ≤ ε` is added: for `ε < 0` the ball is empty. -/
theorem threshold_undoes_linf_adversary {d : ℕ} (s : Fin d → Bool) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    thr '' linfBall (pm s) ε = {pm s} := by sorry

end RobustGeneralization.BernUpper
