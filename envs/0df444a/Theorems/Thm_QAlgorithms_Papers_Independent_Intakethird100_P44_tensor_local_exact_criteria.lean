-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P44_tensor_local_exact_criteria
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P44.tensor_local_exact_criteria
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:27:56.65327+00:00
-- url     : https://prove2.me/theorems/2af44686-dd36-43aa-a0ab-328928f46fbe
-- title:
--   Equivalent exact tensor-local correction criteria
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, and every channel is completely positive and trace preserving on the full matrix algebra. Let $\mathcal N_A(X)=\sum_iE_iXE_i^\dagger$ have a normalized finite Kraus family and let $W:H_L\to H_A\otimes H_B$ be an isometry. Define $W_m=(I\otimes\langle m|)W$ in a fixed basis of $H_B$. Exact correction on this code by a CPTP recovery on $A$ is equivalent to each of the following:
--
--   1. A single normalized environment density $\sigma$ satisfies, for all environment matrices $X$ and all matrices $B$ on $H_B$,
--   $$
--   \sum_{ij}X_{ij}W^\dagger(E_i^\dagger E_j\otimes B)W=\operatorname{Tr}(\sigma X)W^\dagger(I\otimes B)W.
--   $$
--   2. A single complex array $\lambda_{ij}$ satisfies
--   $$
--   W^\dagger(E_i^\dagger E_j\otimes B)W=\lambda_{ij}W^\dagger(I\otimes B)W\quad\text{for all }i,j,B.
--   $$
--   3. A single complex array $\lambda_{ij}$ satisfies
--   $$
--   W_m^\dagger E_i^\dagger E_jW_n=\lambda_{ij}W_m^\dagger W_n\quad\text{for all }i,j,m,n.
--   $$
--
--   The coefficients are uniform in $B,m,n$, and no product-code restriction is imposed.
-- source:
--   Approximate recovery with locality and symmetry constraints, arXiv:1806.10324v2, PDF p. 9, §IV D, Eqs.(49)–(51): exact tensor-local correction criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P44

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P48 (operatorTraceDual)

open QAlgorithms.Papers.Independent.Renew46.P43 (purification)

variable {H K L J E F B : Type*}

variable [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype J] [DecidableEq J]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype B] [DecidableEq B]

/-- PDF pp.9--10, Eqs.(49)--(51): all three equivalent exact criteria.
The state and each lambda_ij are chosen before B,m,n. -/
theorem tensor_local_exact_criteria [Nonempty H] [Nonempty B] [Nonempty L]
    (A : J → Mat H) (hA : IsKrausFamily A)
    (W : Matrix (H × B) L ℂ) (hW : Wᴴ * W = 1) :
    (TensorCorrectable (krausApply A) W ↔
      ∃ sigma : Mat J, IsDensityMatrix sigma ∧ ∀ (X : Mat J) (Y : Mat B),
        (∑ i, ∑ j, X i j •
          (Wᴴ * Matrix.kronecker ((A i)ᴴ * A j) Y * W)) =
        (sigma * X).trace • (Wᴴ * Matrix.kronecker (1 : Mat H) Y * W)) ∧
    (TensorCorrectable (krausApply A) W ↔
      ∃ lambda : J → J → ℂ, ∀ i j (Y : Mat B),
        Wᴴ * Matrix.kronecker ((A i)ᴴ * A j) Y * W =
        lambda i j • (Wᴴ * Matrix.kronecker (1 : Mat H) Y * W)) ∧
    (TensorCorrectable (krausApply A) W ↔
      ∃ lambda : J → J → ℂ, ∀ i j m n,
        (codeSlice W m)ᴴ * (A i)ᴴ * A j * codeSlice W n =
        lambda i j • ((codeSlice W m)ᴴ * codeSlice W n)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P44

end
