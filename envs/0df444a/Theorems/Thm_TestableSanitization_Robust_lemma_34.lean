-- Prove2me | Theorems.Thm_TestableSanitization_Robust_lemma_34
-- name    : TestableSanitization.Robust.lemma_34
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:52:40.283278+00:00
-- url     : https://prove2.me/theorems/d3ff06e7-db29-4068-a9d1-52b7194e03a4
-- title:
--   Lemma 34 — TV distance between uniform balls: $d_{TV}\le\min\{1,\tfrac{\kappa_{d-1}}{\kappa_d}\tfrac\Delta R\}\le\min\{1,\sqrt{\tfrac{d+1}{2\pi}}\tfrac\Delta R\}$
-- statement:
--   Let $d\ge1$, $R>0$ and $x,x'\in\mathbb R^d$, and let $\mu_x=U(B(x,R))$, $\mu_{x'}=U(B(x',R))$ be the uniform distributions on the closed balls of radius $R$ centred at $x$ and $x'$. Let $\Delta=\|x-x'\|$ and $\kappa_m=\pi^{m/2}/\Gamma(m/2+1)$ the volume of the unit ball of $\mathbb R^m$. Then
--   $$d_{TV}(\mu_x,\mu_{x'})\le\min\Big\{1,\frac{\kappa_{d-1}}{\kappa_d}\frac\Delta R\Big\},\qquad \frac{\kappa_{d-1}}{\kappa_d}=\frac{\Gamma(\frac d2+1)}{\sqrt\pi\,\Gamma(\frac{d+1}2)}\le\sqrt{\frac{d+1}{2\pi}},$$
--   and hence $d_{TV}(\mu_x,\mu_{x'})\le\min\{1,\sqrt{(d+1)/(2\pi)}\,\Delta/R\}$. Here $d_{TV}(P,Q)=\sup_A|P(A)-Q(A)|$ over measurable $A$.
--
--   The bound is used to show that the smoothed classifier $x\mapsto\mathbb E_{z\sim U}f(x+\delta z)$ is Lipschitz (Lemma 37), which is what lets the sanitizer's estimator be accurate on a whole cube.
--
--   Differences from the source:
--   - encoding: the input space R^d (a dimension, d ≥ 1 as in Lemma 34) → d : ℕ with the hypothesis 1 ≤ d, points in EuclideanSpace ℝ (Fin d); reason: Lean convention for R^d with the Euclidean norm; excludes only the degenerate d = 0
--   - encoding: U(B(x, R)), the uniform distribution on the closed ball → ballLaw x R, the image of the published uniform law on the closed unit ball under z ↦ x + R • z; reason: for R > 0 this is the normalized Lebesgue measure on B(x, R)
--   - encoding: d_TV as a supremum of |P(A) − Q(A)| over measurable A (real-valued) → tvDist, the same supremum taken in [0, ∞]; reason: the supremum is at most 1, so the value is the same; avoids a real supremum's junk value
--   - encoding: the chain d_TV ≤ min{1, (κ_{d−1}/κ_d)(∆/R)} = min{1, Γ(d/2+1)/(√π Γ((d+1)/2)) · ∆/R} → the first inequality and the equality κ_{d−1}/κ_d = Γ(d/2+1)/(√π Γ((d+1)/2)) as separate conjuncts; reason: the displayed equality of the two minima is the equality of the ratios inside them
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 64 (PDF 66), Lemma 34

import Mathlib
import Definitions.Def_TestableSanitization_Robust_Boundary

open MeasureTheory

namespace TestableSanitization.Robust

theorem lemma_34 (d : ℕ) (hd : 1 ≤ d) (R : ℝ) (hR : 0 < R) (x x' : Pt d) :
    tvDist (ballLaw x R) (ballLaw x' R) ≤
        ENNReal.ofReal (min 1 (kappa (d - 1) / kappa d * (‖x - x'‖ / R))) ∧
      kappa (d - 1) / kappa d =
        Real.Gamma ((d : ℝ) / 2 + 1) / (Real.sqrt Real.pi * Real.Gamma (((d : ℝ) + 1) / 2)) ∧
      kappa (d - 1) / kappa d ≤ Real.sqrt (((d : ℝ) + 1) / (2 * Real.pi)) ∧
      tvDist (ballLaw x R) (ballLaw x' R) ≤
        ENNReal.ofReal (min 1 (Real.sqrt (((d : ℝ) + 1) / (2 * Real.pi)) * (‖x - x'‖ / R))) := by sorry

end TestableSanitization.Robust
