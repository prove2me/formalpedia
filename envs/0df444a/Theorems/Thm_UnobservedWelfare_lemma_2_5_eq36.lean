-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_2_5_eq36
-- name    : UnobservedWelfare.lemma_2_5_eq36
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:50.766426+00:00
-- url     : https://prove2.me/theorems/fbd30add-6e37-4465-8cfb-019c00895805
-- title:
--   Lemma 2.5, energy bound (36) — $V(\bar z^V_\tau)\le\mathbb E_{\pi^V_\tau}[V]\le V(z_0)+\tau m$
-- statement:
--   Let $\tau>0$ and let $V$ be a finite convex Borel energy on $\mathbb R^m_{++}$ with positive finite normalizer $Z_\tau(V)$ and $\mathbb E_{\pi^V_\tau}[\|Z\|_1+|V(Z)|]<\infty$. Let $z_0\in\mathbb R^m_+$ have a finite value $V(z_0)$; if $z_0$ is a boundary point, assume $V$ is convex along the segments joining $z_0$ to points of $\mathbb R^m_{++}$. Then the Gibbs mean lies in $\mathbb R^m_{++}$ and
--   $$V(\bar z^V_\tau)\le\mathbb E_{\pi^V_\tau}[V(Z)]\le V(z_0)+\tau m.\tag{36}$$
--
--   The Gibbs distribution is a soft minimizer: both its expected energy and the energy at its mean are within $\tau m$ of the infimum. This is used for both price rules of Algorithm 1.
--
--   **Formalization Note** $V$ is a real function on $\mathbb R^m$; only its values on $\mathbb R^m_{++}$ and at $z_0$ matter.
--
--   Differences from the source:
--   - generalization: conclusion (36) → (36) together with $\bar z^V_\tau\in\mathbb R^m_{++}$; reason: proved in the last step of the source proof (p.42); dropping the extra clause gives (36)
--   - generalization: at a boundary $z_0$, "$V$ convex along segments joining $z_0$ to points in $\mathbb R^m_{++}$" → only the chord inequality $V((1-s)z_0+sz)\le(1-s)V(z_0)+sV(z)$ for $z\gg0$, $s\in[0,1]$; reason: convexity along each segment implies the chord inequality between its endpoints, and the source proof (p.42) uses only this inequality
--   - encoding: $V:\mathbb R^m_{++}\to\mathbb R$ finite Borel, with an assigned finite value at a boundary $z_0$ → a Borel `V : (Fin m → ℝ) → ℝ`, convex on $\mathbb R^m_{++}$, with the segment condition required only when $z_0\notin\mathbb R^m_{++}$; reason: every source energy extends to such a function; at interior $z_0$ the segment condition is implied by convexity
--   - encoding: positive finite normalizer → `0 < gibbsZ τ V`; reason: a Bochner integral is positive only if the integrand is integrable
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma 2.5 (36), p.19 (PDF p.21); proof in Appendix A.2, p.42 (PDF p.44)

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC
import Definitions.Def_UnobservedWelfare_gibbsMean

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare

/-- **Lemma 2.5, energy bound (36)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma 2.5 (36), p.19 (PDF p.21)). Let `τ > 0` and
let `V` be a finite convex Borel energy on `ℝ^m_{++}` with positive finite normalizer `Z_τ(V)` and
`E_{π^V_τ}[‖Z‖₁ + |V(Z)|] < ∞`. Then for every `z₀ ∈ ℝ^m_+` with a finite value `V(z₀)` — at a
boundary point, `V` being convex along the segments joining `z₀` to points of `ℝ^m_{++}` —
`V(z̄^V_τ) ≤ E_{π^V_τ}[V(Z)] ≤ V(z₀) + τm`.

**Formalization Note** `V` is real-valued on all of `ℝ^m`; only its values on `ℝ^m_{++}` and at
`z₀` matter. `0 < gibbsZ τ V` is "positive finite normalizer" (a non-integrable integrand gives
`0`). The conclusion also records `z̄^V_τ ∈ ℝ^m_{++}` (the last step of the proof, p.42), without
which `V(z̄^V_τ)` would not be a value of the energy. At a boundary `z₀` the segment hypothesis is
the chord inequality `V((1 − s)z₀ + sz) ≤ (1 − s)V(z₀) + sV(z)`, the only form of segment
convexity the proof (p.42) uses; convexity along each segment implies it. -/
theorem lemma_2_5_eq36 {m : ℕ} (τ : ℝ) (hτ : 0 < τ) (V : (Fin m → ℝ) → ℝ) (hVm : Measurable V)
    (hVc : ConvexOn ℝ (posOrthant m) V) (hZ : 0 < gibbsZ τ V)
    (hmom : Integrable (fun z => ∑ i, |z i|) (gibbsMeasure τ V))
    (hint : Integrable V (gibbsMeasure τ V))
    (z0 : Fin m → ℝ) (hz0 : 0 ≤ z0)
    (hseg : z0 ∉ posOrthant m → ∀ z ∈ posOrthant m, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      V ((1 - s) • z0 + s • z) ≤ (1 - s) * V z0 + s * V z) :
    gibbsMean τ V ∈ posOrthant m ∧
    V (gibbsMean τ V) ≤ ∫ z, V z ∂(gibbsMeasure τ V) ∧
    ∫ z, V z ∂(gibbsMeasure τ V) ≤ V z0 + τ * m := by sorry

end UnobservedWelfare
