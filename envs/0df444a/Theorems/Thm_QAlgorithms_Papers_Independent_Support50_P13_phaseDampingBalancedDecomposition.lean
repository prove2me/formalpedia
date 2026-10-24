-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P13_phaseDampingBalancedDecomposition
-- name    : QAlgorithms.Papers.Independent.Support50.P13.phaseDampingBalancedDecomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:24:30.374917+00:00
-- url     : https://prove2.me/theorems/d2a0bd07-3c6d-4c26-8a44-5abae3d0c8f9
-- title:
--   Balanced convex decomposition of a standard-form unital qubit channel
-- statement:
--   Let $\Phi:M_2(\mathbb C)\to M_2(\mathbb C)$ be a unital completely positive trace-preserving linear map in standard form: for the ordered Pauli matrices $\sigma_1,\sigma_2,\sigma_3$, suppose $\Phi(\sigma_j)=\lambda_j\sigma_j$ with real parameters satisfying $1\ge\lambda_3\ge\max(|\lambda_1|,|\lambda_2|)$. Put $\lambda=\lambda_3$, which equals $\max_j|\lambda_j|$ and is nonnegative. Let $r$ be any qubit density matrix. Then there exist $N\ge1$, nonnegative real coefficients $c_i$ with $\sum_{i=1}^Nc_i=1$, and unitary qubit matrices $U_i,W_i$, such that
--
--   $$
--   \begin{gathered}
--   \operatorname{Tr}(\sigma_3U_irU_i^*)=0\quad(1\le i\le N),\\
--   \Phi(A)=\sum_{i=1}^N c_iW_i\Psi_\lambda(U_iAU_i^*)W_i^*
--   \quad\text{for every }A\in M_2(\mathbb C).
--   \end{gathered}
--   $$
--
--   The phase-damping map $\Psi_\lambda$ preserves diagonal entries and multiplies off-diagonal entries by $\lambda$. The family may depend on the given state $r$, but it decomposes the entire channel. This is the convex decomposition used to obtain balanced half-noisy bounds.
-- source:
--   Additivity for a class of unital qubit channels, arXiv:quant-ph/0103156v2, PDF p. 12, Lemma 4, equation (59); standard form on PDF p.11

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Support50.P13

open QAlgorithms.Papers.Independent.Gap48.P03
  (productChannel maximumOutputPNorm holevoQuantity depolarizingNormFactor
    phaseChannel qubitPauli)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Dependency50.P23 (ordinaryClassicalCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- King quant-ph/0103156v2, PDF pp.11-12, (54)-(56), Lemma 4 and (59).
Standard form means Pauli diagonality and lambda_3=max |lambda_i|<=1.
For each given state the chosen family decomposes Phi on ALL operators.
Coefficients here are nonnegative, as required for a convex combination. -/
theorem phaseDampingBalancedDecomposition
    (Phi : Superop (Fin 2) (Fin 2)) (hPhi : IsChannel Phi)
    (hPhiUnital : Phi 1 = 1) (lam : Fin 3 → ℝ)
    (hX : Phi (qubitPauli pauliX) = (lam 0 : ℂ) • qubitPauli pauliX)
    (hY : Phi (qubitPauli pauliY) = (lam 1 : ℂ) • qubitPauli pauliY)
    (hZ : Phi (qubitPauli pauliZ) = (lam 2 : ℂ) • qubitPauli pauliZ)
    (hhigh : lam 2 ≤ 1) (hmax : ∀ i, |lam i| ≤ lam 2)
    (r : Matrix (Fin 2) (Fin 2) ℂ) (hr : IsDensityMatrix r) :
    ∃ (N : ℕ) (c : Fin N → ℝ)
      (U W : Fin N → Matrix.unitaryGroup (Fin 2) ℂ),
      1 ≤ N ∧ (∀ i, 0 ≤ c i) ∧ (∑ i, c i) = 1 ∧
      (∀ i, ((qubitPauli pauliZ) *
        conjSuperop (U i : Matrix (Fin 2) (Fin 2) ℂ) r).trace = 0) ∧
      ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
        Phi A = ∑ i, (c i : ℂ) •
          conjSuperop (W i : Matrix (Fin 2) (Fin 2) ℂ)
            (phaseChannel (1 : Matrix (Fin 2) (Fin 2) ℂ) (lam 2)
              (conjSuperop (U i : Matrix (Fin 2) (Fin 2) ℂ) A)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P13

end
