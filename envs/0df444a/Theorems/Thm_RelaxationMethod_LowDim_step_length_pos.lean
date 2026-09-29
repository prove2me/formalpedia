-- Prove2me | Theorems.Thm_RelaxationMethod_LowDim_step_length_pos
-- name    : RelaxationMethod.LowDim.step_length_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:31:30.03955+00:00
-- url     : https://prove2.me/theorems/f4c71b83-4247-406e-869e-cd9d6ec64bb0
-- title:
--   (3.2) / (3.7) — a non-convergent infinite relaxation sequence has step lengths bounded away from 0
-- statement:
--   Let $A$ be the nonempty solution polytope, with affine span $L_r \neq E_n$ ($r < n$), let $0 < \lambda \leqslant 2$, and let $\{p_\nu\}$ be an infinite relaxation sequence with parameter $\lambda$ that does not converge. Then there is $c > 0$ with
--   $$|p_{\nu+1} - p_\nu| \geqslant c \qquad (\nu = 0, 1, \dots),$$
--   i.e. $\inf_\nu |p_{\nu+1} - p_\nu| > 0$.
--
--   This is claim (a) of the proof of Theorem 2, Case 1, where it leads to a contradiction for $\lambda < 2$; for $\lambda = 2$ it is (3.7), a step of the proof of Theorem 2, Case 2.
--
--   **Formalization Note** The paper proves (3.2) under §7's standing assumptions $r < n$, $0 < \lambda < 2$, and restates it as (3.7) for $\lambda = 2$ in §8 ("Then (3.2) or (3.7) … again holds"). The statement covers $0 < \lambda \leqslant 2$. The infimum is over all $\nu$, as in (3.2).
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), DOI 10.4153/CJM-1954-038-x, p. 400, §7, (3.2); p. 401, §8, (3.7)

import Mathlib
import Definitions.Def_RelaxationMethod_LowDim_RelaxStep

open Filter Topology

namespace RelaxationMethod.LowDim

/-- (3.2), p. 400, and (3.7), p. 401: if `r < n`, `0 < λ ⩽ 2`, and an infinite relaxation
sequence does not converge, then its step lengths are bounded below by a positive constant,
`inf_ν |p_{ν+1} - p_ν| = c > 0`. -/
theorem step_length_pos {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (hr : affineSpan ℝ (polytope a b) ≠ ⊤)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam2 : lam ≤ 2)
    (p : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : ∀ ν, p ν ∉ polytope a b → IsRelaxStep a b lam (p ν) (p (ν + 1)))
    (hinf : ∀ ν, p ν ∉ polytope a b) (hdiv : ¬ ∃ l, Tendsto p atTop (𝓝 l)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν, c ≤ dist (p (ν + 1)) (p ν) := by sorry

end RelaxationMethod.LowDim
