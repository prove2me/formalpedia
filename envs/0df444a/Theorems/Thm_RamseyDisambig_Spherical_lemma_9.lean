-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_lemma_9
-- name    : RamseyDisambig.Spherical.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:25:15.648883+00:00
-- url     : https://prove2.me/theorems/742025ee-d03c-451a-8ede-77db7a221154
-- title:
--   Lemma 9 — Gap preservation under pullback
-- statement:
--   Let $X,Y$ be finite metric spaces, $0<\varepsilon<1/2$, and $\iota_1,\iota_2:Y\to X$ be maps. Suppose $\lambda,\Delta\ge0$ satisfy
--   $$d_X(\iota_1(y),\iota_2(y'))=\lambda d_Y(y,y')+\Delta\quad\text{for all }y,y'\in Y.$$
--   Let $c:X\times X\to\{0,1\}$ be an $\varepsilon$-gap coloring. If
--   $$\lambda\operatorname{diam}(Y)\ge(1-\varepsilon/2)\operatorname{diam}(X),$$
--   then $\widehat c(y,y')=c(\iota_1(y),\iota_2(y'))$ is an $\varepsilon/2$-gap coloring.
--
--   This transfers the endpoint prescriptions along two possibly different maps. No injectivity or nonemptiness assumption is added; when $Y$ is empty its conclusion has no pair constraints.
--
--   Differences from the source:
--   - encoding: finite metric spaces with diameter the supremum of pair distances → Finite metric-space types and a real supremum of the finite pair-distance range, zero for empty spaces; reason: the supremum agrees with finite metric diameter and the empty-space convention adds no pair constraints
--   - encoding: 0 and 1 labels and pullback ĉ → Bool labels and the explicit function (y,y′) ↦ c(ι₁(y),ι₂(y′)); reason: the binary labels and the two maps are unchanged
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Lemma 9, p. 10 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_GapColoring

set_option autoImplicit false

namespace RamseyDisambig.Spherical

/-- Lemma 9, p. 10. Empty finite metric spaces and noninjective maps are included. -/
theorem lemma_9 {X Y : Type*} [MetricSpace X] [MetricSpace Y] [Finite X] [Finite Y]
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (ι₁ ι₂ : Y → X) (scale Δ : ℝ) (hscale : 0 ≤ scale) (hΔ : 0 ≤ Δ)
    (hscale : ∀ y y', dist (ι₁ y) (ι₂ y') = scale * dist y y' + Δ)
    (c : X → X → Bool) (hc : GapColoring ε dist c)
    (hdiam : (1 - ε / 2) * finiteDiameter (dist : X → X → ℝ) ≤
      scale * finiteDiameter (dist : Y → Y → ℝ)) :
    GapColoring (ε / 2) dist (fun y y' => c (ι₁ y) (ι₂ y')) := by sorry

end RamseyDisambig.Spherical
