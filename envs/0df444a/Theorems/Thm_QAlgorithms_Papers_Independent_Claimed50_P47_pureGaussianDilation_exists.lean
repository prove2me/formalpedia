-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P47_pureGaussianDilation_exists
-- name    : QAlgorithms.Papers.Independent.Claimed50.P47.pureGaussianDilation_exists
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:33:51.938545+00:00
-- url     : https://prove2.me/theorems/a42742d0-8e1b-4549-b32e-55d53bf970f9
-- title:
--   Pure Gaussian dilation with at most twice the input mode count
-- statement:
--   Let $n\ge1$ and let $T$ be a Gaussian completely positive trace-preserving map on the full $n$-mode trace-class operator space, with normal unital completely positive dual. Allow arbitrary affine first-moment displacements and write its covariance action as $T(\gamma)=X\gamma X^{\mathsf T}+Y$. There are an integer $0\le m\le2n$, a normalized pure centered Gaussian environmental state $\rho_0$ on $m$ modes with covariance $\gamma_0$, a symplectic matrix $S$, and an implementing Gaussian unitary $U$ such that
--
--   $$
--   T(\tau)=\operatorname{tr}_B\!\left[U(\tau\otimes\rho_0)U^\dagger\right],\qquad
--   \gamma'=S(\gamma\oplus\gamma_0)S^{\mathsf T},\qquad
--   T(\gamma)=[\gamma']_A.
--   $$
--
--   The same environment and unitary work for every trace-class input $\tau$; the covariance identity holds for every physical input covariance $\gamma$. The subsystem $A$ has $n$ modes and $B$ has $m$ modes. This supplies the pure dilation used in the Gaussian MSW correspondence.
-- source:
--   Gaussian quantum channels, arXiv:quant-ph/0505151v1, PDF p. 16, §5.4, Eq. (53): pure Gaussian dilation with at most 2n environment modes

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P47

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P10
  (Phase sigma physicalCovariance pureCovariance thermalCovariance cpMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (PureDensity partialRight boundedUnitaryConjugation dilationReceiver)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-- Eisert--Wolf, PDF p.16, (53): pure Gaussian environmental realization
with at most 2n modes. The witness implements the same channel on every full
trace-class input and has the stated symplectic covariance transformation. -/
theorem pureGaussianDilation_exists {n : ℕ} (hn : 0 < n)
    (Phi : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ →
      Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (X Y : Matrix (Quadratures (Fin n)) (Quadratures (Fin n)) ℝ)
    (hGaussian : IsGaussianChannel Phi X Y) :
    Nonempty (PureGaussianDilation Phi X Y) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P47

end
