-- Prove2me | Theorems.Thm_ReflNewton_LocalQuad_reflPath_sub_step
-- name    : ReflNewton.LocalQuad.reflPath_sub_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:57:25.835967+00:00
-- url     : https://prove2.me/theorems/7ad1fa54-4888-45e1-bdaf-f0ae3876aea5
-- title:
--   Proof of Theorem 13: the reflected step differs quadratically from the Newton step
-- statement:
--   Let $x_*$ be a nondegenerate second-order sufficient point and let $\chi_\alpha\ge0$. For every interior $x$ sufficiently close to $x_*$, every solution $\widehat d$ of the Fig. 11 scaled Newton system, and every $\alpha$ satisfying $|\alpha-1|\le\chi_\alpha\|D(x)^2g(x)\|$, set $d=D(x)\widehat d$. Then, uniformly over those choices,
--
--   $$
--   \|p_{x,d}(\alpha)-d\|\le C\|x-x_*\|^2.
--   $$
--
--   This is the path estimate used when Theorem 11 is applied to the reflected update.
--
--   **Formalization Note** The constant and neighborhood are chosen before $x$, $\widehat d$, and $\alpha$. This estimate requires continuity and local boundedness of the Hessian, but not the additional Lipschitz-Hessian assumption needed for the final quadratic rate. The step-size bound uses $\|D(x)^2g(x)\|$, the corrected Fig. 11 rule; with the printed $\|D(x)g(x)\|$ the estimate fails ($[0,\infty)$, $f(x)=x$, $x_*=0$: $\|p(\alpha)-d\|=\chi_\alpha x^{3/2}$).
-- source:
--   Coleman & Li, On the convergence of interior-reflective Newton methods for nonlinear minimization subject to bounds, Math. Programming 67 (1994), p. 214, proof of Theorem 13, paragraphs beginning 'But applying Lemma 12' and 'But d_k is the Newton step'

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_ReflNewton_LocalQuad_Setting

namespace ReflNewton.LocalQuad

/-- The bound (6.7) makes the reflected Fig. 11 step differ quadratically from its Newton direction
(step-size rule `|α − 1| ≤ χα ‖D² g‖`, the corrected Fig. 11 rule; with `‖D g‖` it is false). -/
theorem reflPath_sub_step {n : ℕ} (l u : Fin n → EReal)
    (hl : ∀ i, l i ≠ ⊤) (hu : ∀ i, u i ≠ ⊥) (hlu : l ≤ u)
    (f : ReflNewton.FirstOrder.E n → ℝ) (D : Set (ReflNewton.FirstOrder.E n)) (hDo : IsOpen D)
    (hFD : LewisTorczon.BoundPS.box l u ⊆ D) (hf : ContDiffOn ℝ 2 f D)
    (xstar : ReflNewton.FirstOrder.E n) (hnd : IsNondegenerate l u f xstar)
    (hsos : SecondOrderSufficient l u f xstar)
    (χα : ℝ) (hχ : 0 ≤ χα) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ,
      ∀ x ∈ ReflNewton.FirstOrder.intBox l u ∩ Metric.ball xstar r,
        ∀ (dh : ReflNewton.FirstOrder.E n) (α : ℝ),
          bHat l u f x dh = -ReflNewton.FirstOrder.dG l u f x →
          |α - 1| ≤ χα * ‖ReflNewton.FirstOrder.dSqG l u f x‖ →
          let d : ReflNewton.FirstOrder.E n := WithLp.toLp 2 fun i => Real.sqrt |ReflNewton.FirstOrder.vVec l u f x i| * dh i
          ‖ReflNewton.FirstOrder.reflPath l u x d α - d‖ ≤ C * ‖x - xstar‖ ^ 2 := by sorry

end ReflNewton.LocalQuad
