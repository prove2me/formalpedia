-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_binaryTestingCharacterization
-- name    : QAlgorithms.Papers.Independent.Information100.P53.binaryTestingCharacterization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:03:15.072975+00:00
-- url     : https://prove2.me/theorems/3ffafc16-90b2-4ce5-a4e0-5e8ad049fa6d
-- title:
--   Lemma 1: attained binary-testing characterization
-- statement:
--   Let $M,N\ge1$, let $S=(\rho_i)_{i=1}^M$ consist of positive semidefinite trace-one matrices on $\mathbb C^N$, and fix $p_i\ge0$ with $\sum_i p_i=1$. Write $P_e(p,S)=1-\sup_D\sum_i p_i\operatorname{Tr}(\rho_i\Lambda_i)$, where the supremum ranges over all POVMs $D=(\Lambda_i)_{i=1}^M$. For density matrices $\psi_0,\psi_1$, define $\alpha_\beta(\psi_0\Vert\psi_1)=\inf\{1-\operatorname{Tr}(\psi_0T):0\preceq T\preceq I,\ \operatorname{Tr}(\psi_1T)\le\beta\}$. Put $\varphi=\operatorname{diag}(p_1\rho_1,\ldots,p_M\rho_M)$. Then
--
--   $$P_e(p,S)=\max_{\mu\succeq0,\ \operatorname{Tr}\mu=1}\alpha_{1/M}\!\left(\varphi\,\middle\Vert\,\frac{I_M}{M}\otimes\mu\right).$$
--
--   The maximum is attained. This cited characterization reduces multiple-state discrimination to constrained binary testing.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 2, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.2, Lemma 1 ([9, Theorem 1]), Eqs.(1)-(2): the exact fixed-prior
optimized error is an attained maximum of constrained binary-testing errors.
The existential witness and universal upper bound express the printed maximum,
not merely a supremum or an inequality. This is a cited background result. -/
theorem binaryTestingCharacterization {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    ∃ mu : Matrix (Fin N) (Fin N) ℂ, IsDensityMatrix mu ∧
      1 - mixedOptSuccess p rho = binaryTypeIError (1 / (M : ℝ))
        (blockEnsembleState p rho) (binaryComparisonState (M := M) mu) ∧
      ∀ nu : Matrix (Fin N) (Fin N) ℂ, IsDensityMatrix nu →
        binaryTypeIError (1 / (M : ℝ)) (blockEnsembleState p rho)
          (binaryComparisonState (M := M) nu) ≤
        binaryTypeIError (1 / (M : ℝ)) (blockEnsembleState p rho)
          (binaryComparisonState (M := M) mu) := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
