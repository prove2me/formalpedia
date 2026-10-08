-- Prove2me | Theorems.Thm_ReflNewton_LocalQuad_lemma_12
-- name    : ReflNewton.LocalQuad.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:36.858848+00:00
-- url     : https://prove2.me/theorems/a176db55-f004-4571-bd22-8cc63c9631e6
-- title:
--   Lemma 12: the Newton step approaches the active bounds at unit length
-- statement:
--   Let $x_*$ be nondegenerate and second-order sufficient for the box-constrained problem. Select $\nu(x)=|v(x)|$, and let $d^N(x)$ solve the Newton equation (6.6). There are a neighborhood radius $r>0$ and a constant $C$ such that, for every strictly interior $x\in B(x_*,r)$, the equation has exactly one solution and, at every index $j$ that is not free at $x_*$,
--
--   $$
--   d_j^N(x)\ne0,\qquad
--   \left|1-\frac{|v_j(x)|}{|d_j^N(x)|}\right|
--   \le C\|x_*-x\|.
--   $$
--
--   The estimate says the first breakpoint in each active coordinate lies near a unit Newton step, which controls the reflected path in Theorem 13.
--
--   **Formalization Note** The equation is represented directly, without a matrix inverse. The nonzero component is asserted before using the breakpoint ratio, so real division does not silently return zero on a zero Newton component.
-- source:
--   Coleman & Li, On the convergence of interior-reflective Newton methods for nonlinear minimization subject to bounds, Math. Programming 67 (1994), p. 213, Lemma 12 and (6.6)–(6.7)

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_ReflNewton_LocalQuad_Setting

namespace ReflNewton.LocalQuad

/-- Lemma 12: the constraint-normal Newton components reach their faces at a nearly unit step. -/
theorem lemma_12 {n : ℕ} (l u : Fin n → EReal)
    (hl : ∀ i, l i ≠ ⊤) (hu : ∀ i, u i ≠ ⊥) (hlu : l ≤ u)
    (f : ReflNewton.FirstOrder.E n → ℝ) (D : Set (ReflNewton.FirstOrder.E n)) (hDo : IsOpen D)
    (hFD : LewisTorczon.BoundPS.box l u ⊆ D) (hf : ContDiffOn ℝ 2 f D)
    (xstar : ReflNewton.FirstOrder.E n) (hnd : IsNondegenerate l u f xstar)
    (hsos : SecondOrderSufficient l u f xstar) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ,
      ∀ x ∈ ReflNewton.FirstOrder.intBox l u ∩ Metric.ball xstar r,
        (∃! d : ReflNewton.FirstOrder.E n, newtonEq l u f x d) ∧
        ∀ d : ReflNewton.FirstOrder.E n, newtonEq l u f x d →
          ∀ j : Fin n, j ∉ freeSet l u xstar →
            d j ≠ 0 ∧
            abs (1 - abs (ReflNewton.FirstOrder.vVec l u f x j) / abs (d j)) ≤ C * ‖xstar - x‖ := by sorry

end ReflNewton.LocalQuad
