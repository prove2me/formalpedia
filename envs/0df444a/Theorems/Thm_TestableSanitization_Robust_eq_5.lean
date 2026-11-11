-- Prove2me | Theorems.Thm_TestableSanitization_Robust_eq_5
-- name    : TestableSanitization.Robust.eq_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:53:41.729871+00:00
-- url     : https://prove2.me/theorems/53b0a04f-4ae8-439a-b7e1-76c37bee6402
-- title:
--   §4.1, Eq. (5) — on the estimator's accuracy event, $\max\{D(\partial g^f_r),\Pr[g^f\neq f]\}\le\mathrm{Iso}_{D,L}(f,b)+\Pr[\|x\|>\mu/\tau]\le\mathrm{NS}_{D,L}(f)/b+\tau$
-- statement:
--   Let $d\ge1$, $0<r<L$, with $s$, $b$, $e$ as in (1) ($0<e\le1/8$); let $\mu>0$ and $\tau\in(0,1)$, and let $D$ be a probability distribution on $\mathbb R^d$ with $\mathbb E_{x\sim D}\|x\|\le\mu$. Let $f$ be a measurable classifier and $\hat\phi:\mathbb R^d\to\mathbb R$ any function that is uniformly $e$-accurate for $\phi_{f,s}$ on the cube $[-A,A]^d$, $A=r+\mu/\tau$:
--   $$|\hat\phi(y)-\phi_{f,s}(y)|\le e\quad\text{whenever } |y_i|\le A \text{ for all } i.$$
--   Let the sanitized classifier be $g^f(y)=-f(y)$ if $\hat\phi(y)>0.6$ and $g^f(y)=f(y)$ otherwise. Then
--   $$\max\{D(\partial g^f_r),\ \Pr_{x\sim D}[g^f(x)\neq f(x)]\}\le\mathrm{Iso}_{D,L}(f,b)+\Pr_{x\sim D}[\|x\|>\mu/\tau]\le\frac{\mathrm{NS}_{D,L}(f)}b+\tau .$$
--
--   In the paper $\hat\phi=\hat\phi_{f,s}$ is the estimator of Lemma 9 on its accuracy event (probability $1-\zeta/8$). Display (5) bounds both the boundary mass and the honest loss of the output by the isolation probability at the testing radius, which is what the isolation test controls; it is the soundness core of Theorem 1.
--
--   Differences from the source:
--   - generalization: the estimator ϕ̂_{f,s} of Lemma 9 (A = r + µ/τ, δ = s, ε = e) on its event of uniform e-accuracy on [−A, A]^d → an arbitrary function phiHat with |phiHat y − ϕ_{f,s}(y)| ≤ e for every y in the cube; reason: the displayed argument uses only this accuracy; the estimator on its accuracy event is an instance, so the Lean statement specializes to the paper's
--   - encoding: the input space R^d (a dimension, d ≥ 1 as in Lemma 34) → d : ℕ with the hypothesis 1 ≤ d, points in EuclideanSpace ℝ (Fin d); reason: Lean convention for R^d with the Euclidean norm; excludes only the degenerate d = 0
--   - encoding: L, s, b, e as in (1); µ, τ from Theorem 8 (r, µ > 0, τ ∈ (0, 1)); θ = 0.6; g^f from Algorithm 2 → hypotheses 0 < r < L, 0 < e ≤ 1/8, 0 < µ, 0 < τ < 1, s = sParam d L r, b = bParam d L r, threshold 3/5, and g given by the hypothesis hg; reason: the definitions of (1), Theorem 8 and Algorithm 2
--   - encoding: E_{x∼D}‖x‖ ≤ µ → ∫⁻ x, ENNReal.ofReal ‖x‖ ∂D ≤ ENNReal.ofReal µ; reason: the expectation of a nonnegative variable as a lower Lebesgue integral; no integrability side condition
--   - encoding: a Borel-measurable classifier f : R^d → {±1} (§2 standing assumption) → f : Pt d → ℝ with IsClassifier f (Measurable f and every value is 1 or -1); reason: the two labels ±1 as reals; same functions
--   - encoding: probabilities and expectations as real numbers → measures of sets and lower Lebesgue integrals in [0, ∞] (ENNReal), compared with ENNReal.ofReal of the real bounds; reason: the values lie in [0, 1]; ENNReal avoids integrability side conditions, and the measure of a possibly non-measurable set is its outer measure, which can only make an upper bound stronger
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 25 (PDF 27), §4.1, proof of Theorem 8, Eq. (5)

import Mathlib
import Definitions.Def_TestableSanitization_Robust_Boundary
import Definitions.Def_TestableSanitization_Robust_Params

open MeasureTheory

namespace TestableSanitization.Robust

theorem eq_5 (d : ℕ) (hd : 1 ≤ d) (r L e μ τ : ℝ) (hr : 0 < r) (hL : r < L) (he : 0 < e)
    (he' : e ≤ 1 / 8) (hμ : 0 < μ) (hτ : 0 < τ) (hτ' : τ < 1)
    (D : Measure (Pt d)) [IsProbabilityMeasure D]
    (hD : ∫⁻ x, ENNReal.ofReal ‖x‖ ∂D ≤ ENNReal.ofReal μ)
    (f : Pt d → ℝ) (hf : IsClassifier f) (phiHat : Pt d → ℝ)
    (hacc : ∀ y : Pt d, (∀ i, |y i| ≤ r + μ / τ) → |phiHat y - lns f (sParam d L r) y| ≤ e)
    (g : Pt d → ℝ) (hg : g = fun y => if 3 / 5 < phiHat y then -f y else f y) :
    max (boundaryMass D r g) (D {x | g x ≠ f x}) ≤
        Iso D L f (bParam d L r) + D {x | μ / τ < ‖x‖} ∧
      Iso D L f (bParam d L r) + D {x | μ / τ < ‖x‖} ≤
        NS D L f / ENNReal.ofReal (bParam d L r) + ENNReal.ofReal τ := by sorry

end TestableSanitization.Robust
