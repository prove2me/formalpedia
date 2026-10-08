-- Prove2me | Theorems.Thm_ReflNewton_LocalQuad_step_is_newton_step
-- name    : ReflNewton.LocalQuad.step_is_newton_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:57:15.960566+00:00
-- url     : https://prove2.me/theorems/5c80a8b4-fc18-4ab1-8aa0-cd9ae2f42751
-- title:
--   Pages 212–213: a local scaled step is Newton for one member of the family
-- statement:
--   Let $x_*$ be a nondegenerate second-order sufficient point. In a sufficiently small neighborhood of $x_*$, take an interior point $x$ and any scaled direction $\widehat d$ satisfying $\widehat B(x)\widehat d=-D(x)g(x)$. Then some admissible $\nu$ from (6.4) makes $d=D(x)\widehat d$ a Newton step for $F_\nu$:
--
--   $$
--   \nabla F_\nu(x)d=-F_\nu(x).
--   $$
--
--   This identifies the algorithmic direction with a member of the finite family used in Theorem 11.
--
--   **Formalization Note** The choice of $\nu$ is allowed to depend on $x$ and the direction, while admissibility is fixed by $x_*$. Strict interiority prevents a zero scaling diagonal.
-- source:
--   Coleman & Li, On the convergence of interior-reflective Newton methods for nonlinear minimization subject to bounds, Math. Programming 67 (1994), pp. 212–213, paragraph after Theorem 11 and paragraph preceding Lemma 12

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_ReflNewton_LocalQuad_Setting

namespace ReflNewton.LocalQuad

/-- The Fig. 11 scaled step solves a Newton equation for one member of (6.3). -/
theorem step_is_newton_step {n : ℕ} (l u : Fin n → EReal)
    (hl : ∀ i, l i ≠ ⊤) (hu : ∀ i, u i ≠ ⊥) (hlu : l ≤ u)
    (f : ReflNewton.FirstOrder.E n → ℝ) (D : Set (ReflNewton.FirstOrder.E n)) (hDo : IsOpen D)
    (hFD : LewisTorczon.BoundPS.box l u ⊆ D) (hf : ContDiffOn ℝ 2 f D)
    (xstar : ReflNewton.FirstOrder.E n) (hnd : IsNondegenerate l u f xstar)
    (hsos : SecondOrderSufficient l u f xstar) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ ReflNewton.FirstOrder.intBox l u ∩ Metric.ball xstar r,
        ∀ dh : ReflNewton.FirstOrder.E n, bHat l u f x dh = -ReflNewton.FirstOrder.dG l u f x →
          ∃ c : Fin n → NuChoice, Admissible l u f xstar c ∧
            fderiv ℝ (Fnu l u f c) x
              (WithLp.toLp 2 fun i => Real.sqrt |ReflNewton.FirstOrder.vVec l u f x i| * dh i) =
              -Fnu l u f c x := by sorry

end ReflNewton.LocalQuad
