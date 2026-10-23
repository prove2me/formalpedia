-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_largeSubspace_fidelity
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.largeSubspace_fidelity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:22:24.922291+00:00
-- url     : https://prove2.me/theorems/6a702e34-c998-4070-ab63-4bfe575965a4
-- title:
--   Proposition 4.5 / (54)–(57): large subspace with high minimum fidelity
-- statement:
--   Let $T$ be a CPTP endomorphism of a complex system of dimension $d\ge1$, let $\rho$ be a density matrix, and let $1\le k\le d$. There is an isometry $V:\mathbb C^k\to\mathbb C^d$, with $P=VV^*$, such that the compressed CPTP channel is
--   $$T_k(X)=V^*T(VXV^*)V+\frac{\operatorname{tr}((I-P)T(VXV^*))}{k}I_k.$$
--   For this same subspace the minimum normalized pure-state fidelity satisfies
--   $$F_{\min}(T_k)\ge1-\frac{1-F_e(\rho,T)}{1-q}$$
--   with $q=k\|\rho\|_\infty$ whenever this $q<1$, and also with $q=(1+\log_2d-S(\rho))/(\log_2d-\log_2k)$ whenever $k<d$ and this second $q<1$. The guards are independent. Entropy is in bits and $F_e$ is squared. The guarded estimates supply the subspace selection needed for capacity equivalences; unguarded printed denominators are corrected explicitly.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 17, Proposition 4.5 / (54)–(57): large subspace with high minimum fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap20.P07

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize rankOne tensorApply)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation isometryCoeff conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (stabilizedTraceClassNorm traceClassTensorMap traceClassChannelPower
   transpose transposeBound TraceLinear tracePair MeasurePrepare)

open QAlgorithms.Papers.Independent.Gap48.P29 (fe FiniteCPMap)

/-- PDF pp.17--18, Proposition 4.5, (54)--(57). Printed denominators lacked
necessary guards. Changed: 1<=k<=d, with each q<1 guard independently applied,
and k<d for the entropy quotient. The same chosen range satisfies both estimates.
The half-space application of (55) is 1-2(1-Fe), correcting p.18's reciprocal typo. -/
theorem largeSubspace_fidelity (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (hkd : k ≤ d)
    (T : Superop (Fin d) (Fin d)) (hT : IsChannel T)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    ∃ V : Matrix (Fin d) (Fin k) ℂ, V.conjTranspose * V = 1 ∧
      IsChannel (compressedChannel V T) ∧
      ((k : ℝ) * specNorm rho < 1 →
        1 - (1 - fe rho T) / (1 - (k : ℝ) * specNorm rho) ≤
          minimumFidelity k (compressedChannel V T)) ∧
      (k < d → let q := (1 + Real.logb 2 d - vnEntropy rho) /
        (Real.logb 2 d - Real.logb 2 k)
        q < 1 → 1 - (1 - fe rho T) / (1 - q) ≤ minimumFidelity k (compressedChannel V T)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
