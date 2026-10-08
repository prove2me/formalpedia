-- Prove2me | Theorems.Thm_TalagrandConc_LinearSuprema_eq_8_1_3
-- name    : TalagrandConc.LinearSuprema.eq_8_1_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:34.649452+00:00
-- url     : https://prove2.me/theorems/f5a4e142-c24b-4c8d-82ed-aa1583aa864a
-- title:
--   Eq. (8.1.3) — a near point of A(a) whose disagreement set has small α-weight
-- statement:
--   Let $\mathcal F$ be a family of real $N$-tuples with $\sigma=\sup_{\alpha\in\mathcal F}\|\alpha\|_2<\infty$,
--   where $\|\alpha\|_2=(\sum_i\alpha_i^2)^{1/2}$, and let $r=(r_i)_{i\le N}$ be real. On $[0,1]^N$ set
--   $Z(x)=\sup_{\alpha\in\mathcal F}\sum_i\alpha_i(r_i+x_i)$ and, for $a\in\mathbb R$,
--   $A(a)=\{y\in[0,1]^N: Z(y)\le a\}$. Write $f_c(A,x)$ for the Euclidean distance from $0$ to the
--   convex hull of the mismatch vectors $U_A(x)$ (Section 4.1).
--
--   Assume $A(a)$ is nonempty, and let $x\in[0,1]^N$ and $\alpha\in\mathcal F$. Then there is
--   $y\in A(a)$ such that, with $I=\{i\le N: y_i\neq x_i\}$,
--   $$\sum_{i\in I}|\alpha_i|\le\|\alpha\|_2\,f_c(A(a),x)\le\sigma f_c(A(a),x).$$
--
--   This is the step of the proof of (8.1.2) that converts the convex-hull distance into a bound on
--   how much a single linear form can change when moving from $x$ to a point of $A(a)$.
--
--   **Formalization Note** The page writes $y\in A(x)$; the set meant is $A(a)$. Nonemptiness of
--   $A(a)$ is added: for empty $A(a)$ no witness $y$ exists, $f_c=+\infty$ and (8.1.2) is trivial.
--   Both inequalities are stated in $[0,\infty]$; with $A(a)\neq\varnothing$, $f_c(A(a),x)$ is finite.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 156, Eq. (8.1.3)

import Mathlib
import Definitions.Def_TalagrandConc_LinearSuprema_Basic

namespace TalagrandConc.LinearSuprema

theorem eq_8_1_3 {N : ℕ} (F : Set (Fin N → ℝ))
    (hσfinite : BddAbove (coeffNorm '' F))
    (r x : Fin N → ℝ) (a : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hA : (linearSublevel F r a).Nonempty)
    (α : Fin N → ℝ) (hα : α ∈ F) :
    ∃ y ∈ linearSublevel F r a,
      ENNReal.ofReal (∑ i ∈ Finset.univ.filter (fun i => y i ≠ x i), |α i|) ≤
          ENNReal.ofReal (coeffNorm α) * convexDistance (linearSublevel F r a) x ∧
        ENNReal.ofReal (coeffNorm α) * convexDistance (linearSublevel F r a) x ≤
          ENNReal.ofReal (sigma F) * convexDistance (linearSublevel F r a) x := by sorry

end TalagrandConc.LinearSuprema
