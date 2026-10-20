-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_minimumError_discrimination
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.minimumError_discrimination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:41:21.377478+00:00
-- url     : https://prove2.me/theorems/1ffe0e75-e7f1-4a28-b0d1-50d4d995eeb7
-- title:
--   §V A Eq.(81): optimal memory-channel discrimination
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $R_0,R_1$ be deterministic $N$-combs on a fixed signature, $N\ge1$, and let $\pi_0,\pi_1\ge0$ with $\pi_0+\pi_1=1$. For binary testers the minimum average discrimination error is
--
--   $$
--   \min_P p_e(P)=\frac{1-\max_{T\text{ satisfying tester normalization}}\|\sqrt T^{\,T}(\pi_0R_0-\pi_1R_1)\sqrt T^{\,T}\|_1}{2}.
--   $$
--
--   Both optima are attained. The statement supplies a maximizing $T$, a POVM $\{E_0,E_1\}$ giving the optimal tester $P_i=\sqrt T E_i\sqrt T$, and the bound for every competing tester. Zero priors are allowed. The norm is $\|A\|_1=\operatorname{Tr}\sqrt{A^\dagger A}$.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 18, §V A Eq.(81): optimal memory-channel discrimination

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF pp.18–19, Eq.(81): an attained maximum, an optimal tester constructed by a
POVM sandwich, and the universal average-error bound. Constants are exactly 1/2.
The square roots are transposed in the objective, not in the tester reconstruction. -/
theorem minimumError_discrimination (s : Signature) (n : ℕ) (hn : 0 < n)
    (R0 R1 : Matrix (Basis s n) (Basis s n) ℂ)
    (h0 : Deterministic n s R0) (h1 : Deterministic n s R1)
    (p0 p1 : ℝ) (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1) (hprior : p0+p1 = 1) :
    ∃ T : Matrix (Basis s n) (Basis s n) ℂ,
      TotalNormalized s n T ∧
      (∀ U, TotalNormalized s n U →
        traceNorm (coherentSandwich U ((p0 : ℂ) • R0 - (p1 : ℂ) • R1)) ≤
        traceNorm (coherentSandwich T ((p0 : ℂ) • R0 - (p1 : ℂ) • R1))) ∧
      ∃ E : Fin 2 → Matrix (Basis s n) (Basis s n) ℂ,
        POVM E ∧
        let P := fun i => matrixSqrt T * E i * matrixSqrt T
        CombTester s n 2 P ∧
        discriminationError s n R0 R1 p0 p1 P =
          (1 - traceNorm (coherentSandwich T ((p0 : ℂ) • R0 - (p1 : ℂ) • R1))) / 2 ∧
        ∀ P', CombTester s n 2 P' →
          (1 - traceNorm (coherentSandwich T ((p0 : ℂ) • R0 - (p1 : ℂ) • R1))) / 2 ≤
            discriminationError s n R0 R1 p0 p1 P' := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
