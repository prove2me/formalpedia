-- Prove2me | Theorems.Thm_SublinearPauli_Fidelity_sublinear_fidelity_estimation
-- name    : SublinearPauli.Fidelity.sublinear_fidelity_estimation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:52:12.727551+00:00
-- url     : https://prove2.me/theorems/cfdf546b-4e8a-472a-aa4e-366b1d0fa5e9
-- title:
--   Theorem 1 — sublinear fidelity estimation with Pauli basis measurements, $n=O\bigl(2^{\lambda N}\sqrt3^{(1-\lambda)N}\varepsilon^{-2}\log\frac1\delta\bigr)$
-- statement:
--   Let $\lambda=\frac{1+\sqrt{33}}8$ and $A_N=2^{\lambda N}(\sqrt3)^{(1-\lambda)N}$. Fix a number of qubits $N$, a known target density matrix $\rho$, an unknown lab density matrix $\sigma$, an accuracy $\varepsilon>0$ and a failure probability $0<\delta<1$. Run protocol P1 on $k$ independent batches of $b$ copies of $\sigma$ each,
--   $$b=\Bigl\lceil\frac{3A_N}{\varepsilon^2}\Bigr\rceil,\qquad k=2\Bigl\lceil9\log\frac1\delta\Bigr\rceil+1,$$
--   with every basis sampled uniformly from $\{X,Y,Z\}^{\otimes N}$ independently of $\rho$ and $\sigma$, and output the median of the $k$ batch outputs. Then
--   $$\Pr\Bigl[\bigl|\,\mathrm{output}-\operatorname{Tr}[\rho\sigma]\,\bigr|\le\varepsilon\Bigr]\ge1-\delta,$$
--   using $n=bk$ copies; for $\varepsilon\le1$ and $\delta\le\tfrac12$, $n\le 90\,A_N\varepsilon^{-2}\log\frac1\delta$, so
--   $$n=O\Bigl(\frac{2^{\lambda N}\sqrt3^{(1-\lambda)N}}{\varepsilon^2}\log\frac1\delta\Bigr).$$
--
--   The target may be any mixed state, in which case $\operatorname{Tr}[\rho\sigma]$ is the overlap (the fidelity when $\rho$ is pure). Since $A_N=d^{0.9674\ldots}$, this is the first worst-case sublinear fidelity estimator with Pauli basis measurements.
--
--   **Formalization Note** The probability is the exact product Born law of the $n$ records (basis and outcome of every copy). The constants $3$ and $9$ instantiate the $O(\cdot)$: $3$ is the batch constant of the proof (Chebyshev failure at most $1/3$), and $9$ makes the Hoeffding bound $e^{-k/18}$ on the median failure at most $\delta$.
--
--   Differences from the source:
--   - reading: "Protocol P1" with $n=O(\cdot)\log\frac1\delta$ copies → P1 amplified by the median of independent batches, as in the proof on p.12; reason: the boxed P1 on p.6 is a single mean, and the $\log\frac1\delta$ factor is obtained in the proof by median-of-means.
--   - generalization: $n=O\bigl(A_N\varepsilon^{-2}\log\frac1\delta\bigr)$ → the explicit $b=\lceil3A_N/\varepsilon^2\rceil$, $k=2\lceil9\log\frac1\delta\rceil+1$, $n=bk$; reason: explicit constants imply the $O(\cdot)$ statement ($n\le90A_N\varepsilon^{-2}\log\frac1\delta$ for $\varepsilon\le1$, $\delta\le\frac12$).
--   - encoding: $\langle\rho,\sigma\rangle=\operatorname{Tr}[\rho\sigma]$ → its real part; reason: the trace is real for Hermitian $\rho,\sigma$.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #230 (October 2026), PDF sha256 a007d4d449494d7b3589233107d1fc0190d256341e1bcbb1b95965363d6e10c4, p.11, Theorem 1 (proof pp.11–12; informal version p.2; protocol P1 p.6)

import Mathlib
import Definitions.Def_SublinearPauli_Fidelity_Protocol

open ClassicalShadow.Linear

namespace SublinearPauli.Fidelity

/-- **Theorem 1** (Sublinear fidelity estimation with Pauli basis measurements), p.11, with the
median-of-means amplification of its proof (p.12) made explicit. For every number of qubits `N`,
every known target density matrix `ρ`, every unknown lab density matrix `σ`, every `ε > 0` and
every `0 < δ < 1`: protocol P1 run on `k = 2⌈9 log(1/δ)⌉ + 1` independent batches of
`b = ⌈3 A_N / ε²⌉` copies of `σ` (bases sampled uniformly, independently of `ρ` and `σ`), whose
output is the median of the `k` batch outputs, satisfies
`Pr[ |output − Tr[ρσ]| ≤ ε ] ≥ 1 − δ`, with `n = bk = O(A_N ε^{-2} log(1/δ))` copies,
`A_N = 2^{λN}(√3)^{(1−λ)N}`, `λ = (1 + √33)/8`. -/
theorem sublinear_fidelity_estimation (N : ℕ) (ρ σ : Op N)
    (hρ : WildeQIT.IsDensityOperator ρ) (hσ : WildeQIT.IsDensityOperator σ)
    (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ successProb ρ σ (blockSize N ε) (numBlocks δ) ε := by sorry

end SublinearPauli.Fidelity
