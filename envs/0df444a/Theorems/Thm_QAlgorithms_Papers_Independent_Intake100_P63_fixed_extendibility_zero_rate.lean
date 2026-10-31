-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_fixed_extendibility_zero_rate
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.fixed_extendibility_zero_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:25:23.861151+00:00
-- url     : https://prove2.me/theorems/74b1ae1b-f253-49e7-89ad-18a0c5e922e2
-- title:
--   §IV, unnumbered example: fixed-extendibility families can have zero rate
-- statement:
--   Let $H_A,H_B$ be nonzero finite-dimensional complex Hilbert spaces and fix a positive integer $k$ before varying the copy count. A state on $A:B$ is k-extendible if it admits a normalized extension to $A:B_1:\cdots:B_k$ symmetric in the B systems and having the original state as each A:B_j marginal. For every normalized bipartite state $\rho$, let $E_{k,n}$ be the infimum of $D_2(\rho^{\otimes n}\Vert\omega)$ over k-extendible states on the grouped blocks $H_A^{\otimes n}:H_B^{\otimes n}$. Then
--   $$
--   \inf_{n\ge1}\frac{E_{k,n}}n=\lim_{n\to\infty}\frac{E_{k,n}}n=0.
--   $$
--
--   Thus the five state-set axioms do not imply general faithfulness. The conclusion includes all states, rather than only entangled states.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 28, §IV, unnumbered example: fixed-extendibility families can have zero rate

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.28 Eqs.(185)--(187), unnumbered example: every state's rate is zero
for each FIXED positive extension level. The copy number is not the extension level. -/
theorem fixed_extendibility_zero_rate {A B : Type*}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (k : ℕ) (hk : 0 < k) (rho : Mat (A × B)) (hrho : IsDensityMatrix rho) :
    regularizedSetEntropy (extendibleFamily (A := A) (B := B) k) rho = 0 ∧
    Tendsto (fun n => setEntropy (extendibleFamily (A := A) (B := B) k n)
      (piKron n rho) / (n : ℝ≥0∞)) atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
