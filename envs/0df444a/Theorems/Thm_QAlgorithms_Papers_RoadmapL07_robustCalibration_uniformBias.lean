-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL07_robustCalibration_uniformBias
-- name    : QAlgorithms.Papers.RoadmapL07.robustCalibration_uniformBias
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:33:54.903421+00:00
-- url     : https://prove2.me/theorems/497dc323-a3d9-47b5-83cf-d0f91556ca4b
-- title:
--   Global-Clifford robust-shadow calibration: simultaneous asymptotic bias bound
-- statement:
--   Consider Protocol 1 of Chen, Yu, Zeng and Flammia on $n\ge 1$ qubits, with Hilbert space dimension $d=2^n$. The same completely positive, trace-preserving noise channel $\Lambda$ acts after each ideal global Clifford gate; fixed computational-basis measurement noise is absorbed into $\Lambda$. Calibration perfectly prepares $|0\rangle^{\otimes n}$. The full Clifford group modulo global phase is sampled uniformly and calibration shots are independent and identically distributed.
--
--   Let $\varepsilon>0$ and $0<\delta\le 1$. Define the Z-basis average fidelity by $F_Z(\Lambda)=d^{-1}\sum_b\langle b|\Lambda(|b\rangle\langle b|)|b\rangle$, and suppose $F_Z(\Lambda)>1/d$. Set
--   $$
--   A=\frac{(1+\varepsilon^2)(1+1/d)^2}{\varepsilon^2(F_Z(\Lambda)-1/d)^2}.
--   $$
--   The printed sample scale in Theorem 7 is $R_{\rm printed}=136\ln(2/\delta)A$. Interpret its real-valued batch parameters operationally as positive integers $N\ge\lceil68A\rceil$ and $K\ge\lceil2\ln(2/\delta)\rceil$, with actual calibration count $R=NK$.
--
--   For each recorded ideal Clifford $U$ and noisy outcome $b$, compute $\widehat f^{(r)}=(d|\langle b|U(|0\rangle^{\otimes n})|^2-1)/(d-1)$. Let $\widehat f$ be the median of the $K$ means of batches of $N$ such scores. The estimated inverse sends an operator $X$ to $(\operatorname{Tr}X/d)I+\widehat f^{-1}(X-(\operatorname{Tr}X/d)I)$. Let $\widetilde{\mathcal M}(X)=\mathbb E_U[U^\dagger\mathcal M_Z(\Lambda(UXU^\dagger))U]$, where $\mathcal M_Z$ removes off-diagonal computational-basis entries, and let $O_0=O-(\operatorname{Tr}O/d)I$.
--
--   With probability at least $1-\delta$ over calibration records, $\widehat f\ne0$ and the subsequent single-shot retrieval expectation satisfies, simultaneously for every Hermitian observable $O$ and every density matrix $\rho$,
--   $$
--   \left|\mathbb E_{U,b\mid\rho}[\operatorname{Tr}(O\widehat{\mathcal M}^{-1}(U^\dagger|b\rangle\langle b|U))]-\operatorname{Tr}(O\rho)\right|
--   =\left|\operatorname{Tr}(O\widehat{\mathcal M}^{-1}\widetilde{\mathcal M}(\rho))-\operatorname{Tr}(O\rho)\right|
--   \le\varepsilon\|O_0\|_\infty.
--   $$
--   Here $\|\cdot\|_\infty$ is the operator norm, and the expectation is conditional on the calibration result. This guarantee controls the systematic, asymptotic bias of robust shadow retrieval; it applies to all observables and states on the same successful calibration event.
--
--   **Formalization Note** The statement retains the printed $1+\varepsilon^2$ factor. The source proof's substitution instead gives $(1+\varepsilon)^2$ from the stated variance bound; this discrepancy and the integer rounding interpretation remain subject to independent source moderation. The product of rounded batch parameters is not asserted to equal, or be bounded above by the ceiling of, the printed total scale. The frozen calibration probability law, overlap scores, median and retrieval expectation compute the named protocol directly.
-- source:
--   Robust shadow estimation, arXiv:2011.09636v2, Theorem 7, Eqs. (B24)-(B25), Protocol 1, PDF p. 22. https://arxiv.org/abs/2011.09636v2 . PDF SHA-256: 7eced8a8057b3aad3456a4c90aa4d240a4feaf7ef40639a86bcc7e842c6b9669.

import Definitions.Def_QAlgorithms_Defs_RobustShadowRetrieval
set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapL07

open QAlgorithms.RobustShadow

/-- Chen, Yu, Zeng and Flammia, *Robust shadow estimation*, arXiv:2011.09636v2,
PDF p.22, Theorem 7, Eqs. (B24)--(B25), for Protocol 1 (PDF pp.18--19).
One fixed CPTP noise channel acts after every uniformly sampled global Clifford;
calibration uses perfectly prepared zero states and independent identical shots.
The probability concerns one event giving a meaningful estimated inverse and the
asymptotic bias bound simultaneously for every Hermitian observable and density matrix.
Positive integer batches round the source's real parameters upward: N >= 68 A,
K >= 2 ln(2/delta), where A is the printed B24 factor. The actual count is N*K.
The printed numerator 1+eps^2 is retained. The proof's choice of gamma would instead
yield (1+eps)^2 by its variance estimate; this unresolved proof discrepancy and the
rounding convention require independent source moderation (see MODERATION_NOTES.md).
-/
theorem robustCalibration_uniformBias {n : ℕ}
    [Fintype (QAlgorithms.Clifford.ProjectiveGroup n)]
    (hn : 0 < n)
    (Lambda : Superop (Qubits n) (Qubits n)) (lawful : IsChannel Lambda)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1)
    (hfidelity : ((2 : ℝ) ^ n)⁻¹ < zFidelity Lambda lawful)
    (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    (hbatch : 68 * ((1 + eps ^ 2) * (1 + ((2 : ℝ) ^ n)⁻¹) ^ 2) /
      (eps ^ 2 * (zFidelity Lambda lawful - ((2 : ℝ) ^ n)⁻¹) ^ 2) ≤ (N : ℝ))
    (hbatches : 2 * Real.log (2 / delta) ≤ (K : ℝ)) :
    calibrationLaw hn hN hK Lambda lawful
      {record | uniformBiasEvent hn hN hK Lambda lawful eps heps record} ≥
        ENNReal.ofReal (1 - delta) := by sorry

end QAlgorithms.Papers.RoadmapL07
