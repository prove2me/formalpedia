-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL13_randomPauli_traceNormRecovery
-- name    : QAlgorithms.Papers.RoadmapL13.randomPauli_traceNormRecovery
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:21:29.732153+00:00
-- url     : https://prove2.me/theorems/896e0c55-eb1b-49f0-ba4c-8f603f546a23
-- title:
--   Random Pauli tomography: trace-norm recovery for Dantzig and Lasso
-- statement:
--   There are positive absolute constants $C,C_0,C_1,C'_0,C'_1$ and a function $\eta:\mathbb N\to[0,1]$ with $\eta(n)\to0$ as $n\to\infty$ such that the following holds. Let $d=2^n$, $1\le r\le d$, and $m\ge1$ satisfy $m\ge Crd(\log d)^6$. Sample $P_1,\ldots,P_m$ independently and uniformly, with replacement, from all $d^2$ unsigned tensor Pauli operators, including the identity. On the real space of Hermitian matrices define $\mathcal A(X)_i=\sqrt{d/m}\,\operatorname{Tr}(P_iX)$ and $\mathcal A^*(v)=\sqrt{d/m}\sum_i v_iP_i$.
--
--   With probability at least $1-\eta(n)$ over this sampling, simultaneously for every positive semidefinite matrix $\rho$ (without a trace or rank restriction), every $z\in\mathbb R^m$, and $y=\mathcal A(\rho)+z$, both conclusions below hold. Write $\rho_r$ for the spectral truncation retaining the largest $r$ eigenvalues, and $\rho_c=\rho-\rho_r$. All optimizations range over Hermitian matrices and permit nonunique minimizers.
--
--   1. For every $\lambda$ satisfying $\|\mathcal A^*(z)\|\le\lambda$, the problem minimizing $\|X\|_{\mathrm{tr}}$ subject to $\|\mathcal A^*(\mathcal A(X)-y)\|\le\lambda$ has a minimizer. Every such minimizer $\widehat\rho_{\mathrm{DS}}$ satisfies
--   $$
--   \|\widehat\rho_{\mathrm{DS}}-\rho\|_{\mathrm{tr}}\le C_0r\lambda+C_1\|\rho_c\|_{\mathrm{tr}}.
--   $$
--   2. For every $\mu>0$ satisfying $\|\mathcal A^*(z)\|\le\mu/2$, the problem minimizing $\frac12\|\mathcal A(X)-y\|_2^2+\mu\|X\|_{\mathrm{tr}}$ has a minimizer. Every such minimizer $\widehat\rho_{\mathrm{Lasso}}$ satisfies
--   $$
--   \|\widehat\rho_{\mathrm{Lasso}}-\rho\|_{\mathrm{tr}}\le C'_0r\mu+C'_1\|\rho_c\|_{\mathrm{tr}}.
--   $$
--   Here $\|\cdot\|$ is the operator norm, $\|\cdot\|_2$ is the Euclidean vector norm, and $\|X\|_{\mathrm{tr}}=\operatorname{Tr}\sqrt{X^\dagger X}$ is the full trace norm. The two bounds separate noise from the spectral tail and apply to full-rank inputs as well as exactly low-rank ones.
--
--   **Formalization Note** The paper's qualitative “high probability” is represented by a vanishing failure function uniform in $r,m$. Positive Lasso regularization is an explicit correction of the omitted $\mu=0$ domain; the source's regularized recovery argument requires it. This correction, the interpretation of unnormalized PSD inputs, and the qualitative probability convention require independent moderation.
-- source:
--   Quantum Tomography via Compressed Sensing: Error Bounds, Sample Complexity, and Efficient Estimators, arXiv:1205.2300v2, Theorem 1, §II.C, PDF p. 5. https://arxiv.org/abs/1205.2300v2 . PDF SHA-256: 58d89ad5a1a2204cf83ba0e4170b6b796f553f95b46bc198e322e223f7f82bb0.

import Definitions.Def_QAlgorithms_Defs_CompressedPauliRecovery
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.RoadmapL13

attribute [local instance] Classical.propDecidable

open QAlgorithms.CompressedTomography

/-- Flammia, Gross, Liu and Eisert, arXiv:1205.2300v2, Theorem 1, PDF/printed
page 5; sampling and variational estimators are Eqs. (1)--(4), page 4.
One random sampling event gives both trace-norm bounds, uniformly over PSD
inputs (not necessarily trace one), arbitrary real noise, and all minimizers.
The qualitative failure bound tends to zero with the number of qubits and is
uniform in the admissible rank and sample count; no numerical rate is supplied.
Source clarification: Lasso uses positive regularization `mu > 0`. The printed
noise condition alone allows `mu = 0`, where arbitrary least-squares minimizers
in an unmeasured direction do not obey the asserted recovery bound. This
domain correction and the unnormalized-input reading await independent moderation.
-/
theorem randomPauli_traceNormRecovery :
    ∃ C C0 C1 C0Lasso C1Lasso : ℝ,
      0 < C ∧ 0 < C0 ∧ 0 < C1 ∧ 0 < C0Lasso ∧ 0 < C1Lasso ∧
      ∃ eta : ℕ → ℝ, (∀ n, 0 ≤ eta n ∧ eta n ≤ 1) ∧
        Filter.Tendsto eta Filter.atTop (nhds 0) ∧
        ∀ (n r m : ℕ) (hr : 1 ≤ r ∧ r ≤ 2 ^ n) (hm : 0 < m),
          C * (r : ℝ) * (2 : ℝ) ^ n * Real.log ((2 : ℝ) ^ n) ^ 6 ≤ (m : ℝ) →
          ((PauliDesign.uniformDesign n m).toOuterMeasure
            {P | ∀ (rho : Matrix (Qubits n) (Qubits n) ℂ) (positive : rho.PosSemidef)
                (z : EuclideanSpace ℝ (Fin m)),
              let y := samplingMap P hm rho positive.isHermitian + z
              let tail := traceNorm (rho - bestRankApproximation rho positive r hr)
              (∀ lam : ℝ, specNorm (samplingAdjoint P hm z) ≤ lam →
                (∃ X : Matrix (Qubits n) (Qubits n) ℂ, IsDantzigSelector P hm y lam X) ∧
                ∀ X : Matrix (Qubits n) (Qubits n) ℂ, IsDantzigSelector P hm y lam X →
                  traceNorm (X - rho) ≤ C0 * (r : ℝ) * lam + C1 * tail) ∧
              (∀ mu : ℝ, 0 < mu → specNorm (samplingAdjoint P hm z) ≤ mu / 2 →
                (∃ X : Matrix (Qubits n) (Qubits n) ℂ, IsMatrixLasso P hm y mu X) ∧
                ∀ X : Matrix (Qubits n) (Qubits n) ℂ, IsMatrixLasso P hm y mu X →
                  traceNorm (X - rho) ≤ C0Lasso * (r : ℝ) * mu + C1Lasso * tail)}).toReal
            ≥ 1 - eta n := by sorry

end QAlgorithms.Papers.RoadmapL13
