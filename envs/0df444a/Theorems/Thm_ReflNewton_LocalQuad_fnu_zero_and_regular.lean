-- Prove2me | Theorems.Thm_ReflNewton_LocalQuad_fnu_zero_and_regular
-- name    : ReflNewton.LocalQuad.fnu_zero_and_regular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:57:10.552031+00:00
-- url     : https://prove2.me/theorems/cf13bd5c-d32c-4f19-b3ae-c870cc8670cd
-- title:
--   Equation (6.3)–(6.4): the local Newton family vanishes and has regular Jacobians
-- statement:
--   Let $x_*$ be a nondegenerate feasible point satisfying $D(x_*)^2g(x_*)=0$ and positive definiteness of the Hessian on its free coordinates. For every admissible choice $\nu$ in (6.4), the function $F_\nu(x)=\operatorname{diag}(\nu(x))g(x)$ is continuously differentiable on the open set $D$ containing the box and satisfies
--
--   $$
--   F_\nu(x_*)=0,\qquad \nabla F_\nu(x_*)\text{ is nonsingular}.
--   $$
--
--   The first two assertions are stated on page 211. Nonsingularity is the regularity condition needed to apply Theorem 11 to this family; it follows from nondegeneracy and the second-order condition.
--
--   **Formalization Note** The theorem assumes $f\in C^2(D)$ and the paper's one-sided extended-real bounds. It does not assume nonsingularity: that is part of the conclusion.
-- source:
--   Coleman & Li, On the convergence of interior-reflective Newton methods for nonlinear minimization subject to bounds, Math. Programming 67 (1994), p. 211, (6.3)–(6.4) and paragraph after (6.4); nonsingularity used in Theorem 13 via Theorem 11

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_ReflNewton_LocalQuad_Setting

namespace ReflNewton.LocalQuad

/-- The family (6.3) vanishes at the second-order point and has nonsingular Jacobians there. -/
theorem fnu_zero_and_regular {n : ℕ} (l u : Fin n → EReal)
    (hl : ∀ i, l i ≠ ⊤) (hu : ∀ i, u i ≠ ⊥) (hlu : l ≤ u)
    (f : ReflNewton.FirstOrder.E n → ℝ) (D : Set (ReflNewton.FirstOrder.E n)) (hDo : IsOpen D)
    (hFD : LewisTorczon.BoundPS.box l u ⊆ D) (hf : ContDiffOn ℝ 2 f D)
    (xstar : ReflNewton.FirstOrder.E n) (hnd : IsNondegenerate l u f xstar)
    (hsos : SecondOrderSufficient l u f xstar) :
    ∀ c : Fin n → NuChoice, Admissible l u f xstar c →
      ContDiffOn ℝ 1 (Fnu l u f c) D ∧
      Fnu l u f c xstar = 0 ∧
      Function.Bijective (fderiv ℝ (Fnu l u f c) xstar) := by sorry

end ReflNewton.LocalQuad
