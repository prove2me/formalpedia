-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL12_directFidelityEstimation_guarantee
-- name    : QAlgorithms.Papers.RoadmapL12.directFidelityEstimation_guarantee
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:21:18.56301+00:00
-- url     : https://prove2.me/theorems/83760002-56e1-43ac-a351-0de8e53b8f60
-- title:
--   Direct fidelity estimation: finite-copy confidence interval and expected copy cost
-- statement:
--   Let $n\ge 0$ be an integer, $d=2^n$, and $\rho=|\psi\rangle\langle\psi|$ for a normalized $n$-qubit pure state $|\psi\rangle$. Let $\sigma$ be any density matrix on the same register, possibly mixed. For each phase-free Hermitian Pauli product $W_k\in\{I,X,Y,Z\}^{\otimes n}$, write $\chi_\tau(k)=\operatorname{Tr}(\tau W_k)/\sqrt d$. The source's fidelity convention is $F(\rho,\sigma)=\operatorname{Tr}(\rho\sigma)$, the square of root fidelity.
--
--   Fix $\varepsilon>0$ and $0<\delta\le1$. Independently draw exactly $\ell=\lceil1/(\varepsilon^2\delta)\rceil$ settings $k_1,\ldots,k_\ell$ with replacement, each with probability $\chi_\rho(k)^2$. Only settings with nonzero target coefficient are drawn. For each draw, measure $W_{k_i}$ separately on
--   $$
--   m_i=\left\lceil\frac{2\log(2/\delta)}{d\chi_\rho(k_i)^2\ell\varepsilon^2}\right\rceil
--   $$
--   fresh independent copies of $\sigma$, obtaining Born-rule outcomes $A_{ij}\in\{-1,+1\}$, independent conditional on the settings. Set
--   $$
--   \widetilde Y=\frac1\ell\sum_{i=1}^{\ell}\frac{\sum_{j=1}^{m_i}A_{ij}}{m_i\sqrt d\,\chi_\rho(k_i)},\qquad m=\sum_{i=1}^{\ell}m_i.
--   $$
--   Then
--   $$
--   \Pr\!\left\{F(\rho,\sigma)\in[\widetilde Y-2\varepsilon,\widetilde Y+2\varepsilon]\right\}\ge1-2\delta,
--   $$
--   and at most $\ell$ distinct observables are measured. The setting-wise and total expected copy costs satisfy
--   $$
--   \mathbb E[m_i]=\sum_{k:\chi_\rho(k)\ne0}\chi_\rho(k)^2m_i(k)
--   \le1+\frac{2d}{\ell\varepsilon^2}\log\frac2\delta,
--   \qquad
--   \mathbb E[m]\le1+\frac1{\varepsilon^2\delta}+\frac{2d}{\varepsilon^2}\log\frac2\delta.
--   $$
--   This protocol estimates the fidelity to an arbitrary known pure target using single-copy Pauli measurements. Its copy cost is random; no efficient classical sampling bound is claimed for general targets.
--
--   **Formalization Note** The finite experiment space fixes exactly $\ell$ setting draws and their setting-dependent numbers of outcomes. Its probability weights are products of the target importance law and conditional Pauli outcome laws. The closed interval is not clipped to $[0,1]$.
-- source:
--   Direct Fidelity Estimation from Few Pauli Measurements, arXiv:1104.4695v3, Fidelity Estimation, equations (3)–(10), PDF p. 2. https://arxiv.org/abs/1104.4695v3 . PDF SHA-256: 4dcff49754dd1eb7964520cf82851fa9d2ce0adba611e33f0f34bdabb2bc3d00.

import Definitions.Def_QAlgorithms_Defs_DirectFidelityEstimation
set_option autoImplicit false

noncomputable section

namespace QAlgorithms.Papers.RoadmapL12

open QAlgorithms.DirectFidelity

/-- Flammia–Liu, Direct Fidelity Estimation from Few Pauli Measurements,
arXiv:1104.4695v3, PDF p.2, equations (3)–(10); assumptions on p.1 and concentration
argument on p.6. The target is pure and normalized; the laboratory state may be mixed.
The experiment draws exactly `settingCount` Pauli settings independently with replacement,
and measures each on `repetitions` fresh copies. Its closed interval contains the source's
squared fidelity `Re Tr(rho * sigma)` with probability at least `1 - 2 * delta`.
The copy bound is in expectation, including the per-setting bound (9).
The appendix's (13)–(14) must restrict the second moment to nonzero target coefficients;
the resulting inequality suffices for this unchanged guarantee. -/
theorem directFidelityEstimation_guarantee {n : ℕ}
    (psi : EuclideanSpace ℂ (Qubits n)) (hpsi : IsState psi)
    (sigma : Matrix (Qubits n) (Qubits n) ℂ) (hsigma : IsDensityMatrix sigma)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1) :
    let rho := pureDensity psi
    let ell := settingCount eps delta heps hdelta
    (open Classical in
      ∑ e : Experiment rho eps delta heps hdelta,
        if (rho * sigma).trace.re ∈
            Set.Icc (estimate rho eps delta heps hdelta e - 2 * eps)
              (estimate rho eps delta heps hdelta e + 2 * eps)
        then experimentLaw psi hpsi sigma hsigma eps delta heps hdelta e else 0) ≥
          1 - 2 * delta ∧
    (∀ settings : Fin ell → characteristicSupport rho,
      (Finset.univ.image settings).card ≤ ell) ∧
    (∑ k : characteristicSupport rho,
      pauliCharacteristic rho k.val ^ 2 *
        (repetitions rho eps delta heps hdelta k : ℝ)) ≤
          1 + (2 * (2 : ℝ) ^ n / ((ell : ℝ) * eps ^ 2)) * Real.log (2 / delta) ∧
    (∑ settings : Fin ell → characteristicSupport rho,
      (∏ i, (importanceLaw psi hpsi (settings i)).toReal) *
        (copyCount rho eps delta heps hdelta settings : ℝ)) ≤
          1 + 1 / (eps ^ 2 * delta) + (2 * (2 : ℝ) ^ n / eps ^ 2) * Real.log (2 / delta)
    := by sorry

end QAlgorithms.Papers.RoadmapL12
