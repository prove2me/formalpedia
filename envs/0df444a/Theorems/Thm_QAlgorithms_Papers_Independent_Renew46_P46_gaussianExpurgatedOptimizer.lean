-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_gaussianExpurgatedOptimizer
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.gaussianExpurgatedOptimizer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:58:56.182981+00:00
-- url     : https://prove2.me/theorems/9bf69070-2f9e-44b2-9081-ab34eb488816
-- title:
--   §V: analytic Gaussian expurgated optimization and (46)
-- statement:
--   Fix $E>0$ and the Gaussian prior of the noiseless coherent channel. Write $q(t)=(1+\sqrt{1+4t^2})/2$ and let $\widetilde\mu_E(s,p)$ be its actual overlap-integral functional. For every $s\ge1$, maximization over $0\le p<1/E$ is attained at
--
--   $$p(s,E)=s^{-1}+E^{-1}-E^{-1}q(E/s),$$
--
--   which lies in that domain. For every real $R$ the reduced objective is
--
--   $$F_R(s)=\widetilde\mu_E(s,p(s,E))-sR=2(E+s-sq(E/s))+s\log q(E/s)-sR.$$
--
--   If $R>0$, then $F_R'(s)=\log q(E/s)-R$, and on $s\ge1$ the stationary equation has the equivalent form
--
--   $$q(E/s)=e^R\ \Longleftrightarrow\ s=\frac{E}{\sqrt{e^{2R}-e^R}}.$$
--
--   The stationary formula does not assert feasibility for every positive rate.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 14, §V: analytic Gaussian expurgated optimization and (46)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section V, PDF p.14, expurgated optimizer and (46). The stationary s
formula is a characterization only on the feasible s>=1 domain, R>0. -/
theorem gaussianExpurgatedOptimizer (E : ℝ) (hE : 0 < E) :
    (∀ s : ℝ, 1 ≤ s → 0 ≤ bestP E s ∧ bestP E s < 1 / E ∧
      (∀ p : ℝ, 0 ≤ p → p < 1 / E →
        gaussianMuEx E s p ≤ gaussianMuEx E s (bestP E s)) ∧
      (∀ R : ℝ, gaussianMuEx E s (bestP E s) - s * R =
        2 * (E + s - s * q (E / s)) + s * Real.log (q (E / s)) - s * R)) ∧
    (∀ R s : ℝ, 0 < R → 1 ≤ s →
      HasDerivAt (fun t => gaussianMuEx E t (bestP E t) - t * R)
        (Real.log (q (E / s)) - R) s ∧
      (q (E / s) = Real.exp R ↔ s = E / Real.sqrt (Real.exp (2 * R) - Real.exp R))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
