-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_eq_1
-- name    : PowerMinUncut.Threshold.eq_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:43:48.971443+00:00
-- url     : https://prove2.me/theorems/8f54f5e4-395b-48d9-8a14-199f74b4ebc9
-- title:
--   §2.3, Eq. (1) — rank-sensitive matrix inequality E_Q J_q(AQ) ≤ b(r,q)/(b(m,q)a(r,q)) E‖AZ_m‖^q
-- statement:
--   Let $q\ge2$ be an integer, let $A:\mathbb R^m\to\mathbb R^k$ have rank $r\ge q$, and let $Q$ be a Haar orthonormal $q$-frame in $\mathbb R^m$. Then
--   $$\mathbb E_Q\,J_q(AQ)\le\frac{b(r,q)}{b(m,q)\,a(r,q)}\,\mathbb E\|AZ_m\|^q,\tag{1}$$
--   with $Z_m$ standard Gaussian in $\mathbb R^m$, $a(d,q)=\mathbb E\chi_d^q$ and $b(d,q)=\prod_{j<q}\mathbb E\chi_{d-j}$. Equal nonzero singular values give equality, and a rank upper bound $R\ge r$ may replace $r$ in (1).
--
--   Applied on great $q$-spheres with rank bound $k-1$, this turns Lemma 5 into the spherical energy bound (2) behind Theorem 2.
--
--   Differences from the source:
--   - encoding: Haar orthonormal q-frame Q in ℝ^m → Gram–Schmidt orthonormalization of q independent standard Gaussian vectors of ℝ^m; reason: Gaussian QR: this is the Haar law on the Stiefel manifold
--   - encoding: equal nonzero singular values → (AᵀA)² = s·AᵀA for some real s; reason: AᵀA has eigenvalues σ_i² and 0; the identity says all nonzero σ_i² equal s
--   - generalization: a rank upper bound R ≥ q may replace r → every real R ≥ r; reason: p. 7 proves b(r, q)/a(r, q) strictly increasing for real r ≥ q, so the bound holds for every real R ≥ r; an integer rank bound (the §2.4 use, R = k − 1) is the special case
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), pp. 6–7, §2.3, Eq. (1)

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Gaussian

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

/-- **§2.3, Eq. (1)**, pp. 6–7. Let `q ≥ 2`, let `A : ℝ^m → ℝ^k` have rank `r ≥ q`, and let `Q` be a
Haar orthonormal `q`-frame in `ℝ^m`. Then `E_Q J_q(AQ) ≤ b(r,q)/(b(m,q) a(r,q)) · E‖AZ_m‖^q`;
any rank upper bound `R ≥ r` may replace `r`; equal nonzero singular values (`(AᵀA)² = s AᵀA`)
give equality. -/
theorem eq_1 (q : ℕ) (hq : 2 ≤ q) (m k : ℕ) (A : E m →L[ℝ] E k)
    (hr : q ≤ Module.finrank ℝ (LinearMap.range (A : E m →ₗ[ℝ] E k))) :
    frameJacMean q A ≤
        bFun (Module.finrank ℝ (LinearMap.range (A : E m →ₗ[ℝ] E k)) : ℝ) q /
          (bFun (m : ℝ) q * aFun (Module.finrank ℝ (LinearMap.range (A : E m →ₗ[ℝ] E k)) : ℝ) q) *
          gaussPowMoment q A ∧
      (∀ R : ℝ, (Module.finrank ℝ (LinearMap.range (A : E m →ₗ[ℝ] E k)) : ℝ) ≤ R →
        frameJacMean q A ≤ bFun R q / (bFun (m : ℝ) q * aFun R q) * gaussPowMoment q A) ∧
      ((∃ s : ℝ, (ContinuousLinearMap.adjoint A ∘L A) ∘L (ContinuousLinearMap.adjoint A ∘L A) =
          s • (ContinuousLinearMap.adjoint A ∘L A)) →
        frameJacMean q A =
          bFun (Module.finrank ℝ (LinearMap.range (A : E m →ₗ[ℝ] E k)) : ℝ) q /
            (bFun (m : ℝ) q * aFun (Module.finrank ℝ (LinearMap.range (A : E m →ₗ[ℝ] E k)) : ℝ) q) *
            gaussPowMoment q A) := by sorry

end PowerMinUncut.Threshold
