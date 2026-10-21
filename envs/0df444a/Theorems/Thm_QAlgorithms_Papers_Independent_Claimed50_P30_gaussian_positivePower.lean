-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P30_gaussian_positivePower
-- name    : QAlgorithms.Papers.Independent.Claimed50.P30.gaussian_positivePower
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:19:28.949454+00:00
-- url     : https://prove2.me/theorems/54fd5884-b9b6-46a2-9ee7-7aac0afbaddb
-- title:
--   Positive powers of actual Gaussian density operators
-- statement:
--   Let $n\ge1$ and let $\rho$ be an actual positive trace-class Gaussian density operator of trace one on the completed $n$-mode oscillator space. Use quadratures with commutators $2i\Omega$ and vacuum covariance $I$. Suppose its physical normal decomposition is
--   $$
--   \rho=U_{u,S}\left[\bigotimes_{k=1}^n\sigma(\nu_k)\right]U_{u,S}^{\dagger},\qquad
--   V=S\left[\bigoplus_{k=1}^n\nu_k I_2\right]S^T,
--   $$
--   where $S\Omega S^T=\Omega$, $\nu_k\ge1$, $u$ is its displacement, and
--   $$
--   \sigma(x)=\sum_{j\ge0}\frac{2}{x+1}\left(\frac{x-1}{x+1}\right)^j|j\rangle\langle j|.
--   $$
--   For a real $p>0$, set
--   $$
--   G_p(x)=\frac{2^p}{(x+1)^p-(x-1)^p},\qquad
--   \Lambda_p(x)=\frac{(x+1)^p+(x-1)^p}{(x+1)^p-(x-1)^p},
--   $$
--   and independently construct
--   $$
--   \rho(p)=U_{u,S}\left[\bigotimes_{k=1}^n\sigma\bigl(\Lambda_p(\nu_k)\bigr)\right]U_{u,S}^{\dagger}.
--   $$
--   Then $\rho^p$ is trace class, $\rho(p)$ is a normalized Gaussian density with displacement $u$, and
--   $$
--   \rho^p=\bigl(\operatorname{Tr}\rho^p\bigr)\rho(p),\qquad
--   \operatorname{Tr}\rho^p=\prod_{k=1}^nG_p(\nu_k),\qquad
--   V(p)=S\left[\bigoplus_{k=1}^n\Lambda_p(\nu_k)I_2\right]S^T.
--   $$
--   These identities connect genuine density powers to physical Gaussian moment data. The pure-mode case $\nu_k=1$ is retained.
--
--   **Formalization Note** Powers use the continuous functional calculus of the bounded positive operator. The normalized power candidate is constructed from thermal densities, not defined by dividing the power by its trace. Convergence of its defining operator series and the trace series is concluded. The theorem does not include $p=0$.
-- source:
--   Computable bounds for the discrimination of Gaussian states, arXiv:0806.1625v2, PDF p. 3, Lemma 1, Eqs. (21)–(23),(32)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Mathlib supplies this C-star functional calculus as a theorem, not a global instance.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P30

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P04 (Covariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- Lemma 1, arXiv:0806.1625v2, PDF p.3, (21)--(23) and (32).
The displayed positive-power condition is p>0. The proof's phrase p>=0 is
not used: the zeroth power of a mixed oscillator density need not have finite trace.
The power state is independently constructed from transformed thermal densities. -/
theorem gaussian_positivePower {n : ℕ} (hn : 0 < n) (W : FockWeylSystem n)
    (A : GaussianState n W) (D : NormalModes A) (p : ℝ) (hp : 0 < p) :
    IsTraceClass (positiveOperatorPower A.rho p) ∧
    TraceSummable (positiveOperatorPower A.rho p) ∧
    Summable (thermalTerm (fun k => spectralLambda p (D.spectrum k))) ∧
    GaussianMoments W (powerState D p) A.mean (powerCovariance D p) ∧
    positiveOperatorPower A.rho p = trace (positiveOperatorPower A.rho p) • powerState D p ∧
    trace (positiveOperatorPower A.rho p) = ((∏ k, spectralG p (D.spectrum k) : ℝ) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P30

end
