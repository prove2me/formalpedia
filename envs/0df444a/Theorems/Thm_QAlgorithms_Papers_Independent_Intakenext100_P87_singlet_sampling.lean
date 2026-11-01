-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P87_singlet_sampling
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P87.singlet_sampling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:22:45.835528+00:00
-- url     : https://prove2.me/theorems/82302601-a4da-4ff0-a9ca-d3a774d60445
-- title:
--   Supplementary Note 6, Claim: estimating the singlet fraction
-- statement:
--   Let $1\le m\le N$ and let $\rho$ be any normalized state of $N$ pairs, allowing arbitrary correlations among the pairs and with an external reference. Uniformly select $m$ distinct positions, and independently choose one uniform axis from $x,y,z$ for each selected pair. Let $K$ count antiparallel outcomes and let $F_{\rm singlet}$ be the mean probability of a local singlet projection over all $N$ pairs. The source's estimator satisfies
--
--   $$\widehat F=\frac{3K-m}{2m},\qquad\mathbb E[\widehat F]=F_{\rm singlet}.$$
--
--   Moreover, for every fixed sample and axis choice, the entire coarse outcome law is unchanged by complete Bell premeasurement. This permits classical sampling analysis. No confidence-width formula or clipping of negative estimates is introduced.
-- source:
--   Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances, arXiv:quant-ph/9803006v5, PDF p. 21, Supplementary Note 6, Claim: estimating the singlet fraction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P87

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P87

open scoped Matrix ComplexConjugate

open QAlgorithms.Measurements

/-- PDF pp.11,20--21, Supplementary Note 6 Claim: the unclipped estimator is unbiased;
its full coarse sampling law equals the Bell-premeasured law for arbitrary correlated inputs. -/
theorem singlet_sampling (N m : ℕ) (hm : 0 < m) (hNm : m ≤ N)
    (rho : Matrix (PairRegister N) (PairRegister N) ℂ) (hrho : IsDensityMatrix rho) :
    meanSingletEstimate rho m = meanLocalSingletWeight rho ∧
    ∀ (s : Fin m ↪ Fin N) (axes : Fin m → Fin 3) (anti : Qubits m),
      pairAxisSampleLaw (bellPinch rho) s axes anti = pairAxisSampleLaw rho s axes anti := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P87

end
