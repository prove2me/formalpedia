-- Prove2me | Theorems.Thm_SketchAttr_LOO_proposition_4_8
-- name    : SketchAttr.LOO.proposition_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:26:57.830173+00:00
-- url     : https://prove2.me/theorems/f8e17233-b888-4e51-b69a-f3ad7aeb3a44
-- title:
--   Proposition 4.8 — trimmed-mean concentration with finite variance
-- statement:
--   Let $X_1,\ldots,X_m$ be independent identically distributed real random variables on a probability space, with mean $\mu$ and finite variance $\sigma^2$, where $\sigma\ge0$. Fix $\delta\in(0,1)$ and suppose $m\ge64\log(16/\delta)$. Then
--   $$\mathbb P\left(\left|\operatorname{Trim}_{\lfloor\log(16/\delta)\rfloor}(X_1,\ldots,X_m)-\mu\right|>7\sigma\sqrt{\frac{\log(16/\delta)}m}\right)\le\delta.$$
--   This is the finite-variance concentration statement cited by the paper. It supplies logarithmic dependence on the failure probability without requiring sub-Gaussian observations. The stated sample bound implies that fewer than half the observations are trimmed from either side, and it excludes $m=0$.
--
--   Differences from the source:
--   - encoding: real random variables with finite variance and a probability-at-least statement → MemLp exponent 2 on an arbitrary probability space and an outer-measure bound on the strict bad event; reason: finite second moment is exactly the source condition and the bad-event formulation retains the source probability guarantee without a measurability loophole
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), p. 13, Proposition 4.8 (citing [OOR25, Theorem 5.1.1]); canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib
import Definitions.Def_SketchAttr_LOO_Trim
open MeasureTheory ProbabilityTheory

namespace SketchAttr.LOO

/-- Proposition 4.8 on an arbitrary probability space; finite second moment
is a hypothesis, not a default-valued variance integral. -/
theorem proposition_4_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (m : ℕ) (X : Fin m → Ω → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ i j : Fin m, IdentDistrib (X i) (X j) P P)
    (hL2 : ∀ i : Fin m, MemLp (X i) 2 P)
    (μ σ : ℝ) (hσ : 0 ≤ σ)
    (hmean : ∀ i : Fin m, (∫ ω, X i ω ∂P) = μ)
    (hvar : ∀ i : Fin m, (∫ ω, (X i ω - μ)^2 ∂P) = σ^2)
    (δ : ℝ) (hδpos : 0 < δ) (hδlt : δ < 1)
    (hm : 64 * Real.log (16/δ) ≤ (m : ℝ)) :
    P {ω | 7*σ*Real.sqrt (Real.log (16/δ)/(m : ℝ)) <
      |trim ⌊Real.log (16/δ)⌋₊ (fun i => X i ω) - μ|} ≤ ENNReal.ofReal δ := by sorry

end SketchAttr.LOO
