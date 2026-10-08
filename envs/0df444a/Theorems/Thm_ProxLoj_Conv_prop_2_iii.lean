-- Prove2me | Theorems.Thm_ProxLoj_Conv_prop_2_iii
-- name    : ProxLoj.Conv.prop_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:37:43.906583+00:00
-- url     : https://prove2.me/theorems/f3b8026b-ff66-40c2-9a71-e24cea27624f
-- title:
--   Proposition 2 (iii), p. 3 — under (H2), the limit points of a proximal run are critical: ω(x⁰) ⊂ crit f
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be proper, lower semicontinuous, with $\inf f>-\infty$ (H1) and continuous on its domain (H2). Let $0<\lambda_-<\lambda_+$, $\lambda_k\in(\lambda_-,\lambda_+)$, and let $(x^k)$ comply with (2). Writing $\omega(x^0)$ for the set of limit points of $(x^k)$,
--   $$\omega(x^0)\subset\operatorname{crit} f=\{x : 0\in\partial f(x)\},$$
--   where $\partial f$ is the limiting subdifferential.
--
--   Every cluster point of the proximal sequence is a limiting-critical point; the sequence need not be bounded (then $\omega(x^0)$ may be empty).
--
--   **Formalization Note** Boundedness of the sequence is not assumed, as on the page. (H3) is dropped. A limit point is a cluster point (`MapClusterPt`) of the sequence.
-- source:
--   Attouch & Bolte, On the convergence of the proximal algorithm for nonsmooth functions involving analytic features, author's version hal-00803898v1, p. 3, Proposition 2 (iii)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope
import Definitions.Def_ProxLoj_Conv_Setting

open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous

namespace ProxLoj.Conv

/-- Proposition 2 (iii), p. 3: under (H2), every limit point of a proximal run is critical,
`ω(x⁰) ⊆ crit f`. -/
theorem prop_2_iii {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hproper : IsProper f)
    (hlsc : LowerSemicontinuous f) (hH1 : H1 f) (hH2 : H2 f)
    (lam : ℕ → ℝ) (lamMinus lamPlus : ℝ) (hstep : StepBounds lam lamMinus lamPlus)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsProxRun f lam x) :
    limitSet x ⊆ crit f := by sorry

end ProxLoj.Conv
