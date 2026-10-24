-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_diagonal_kraus_characterization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.diagonal_kraus_characterization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:45:37.780527+00:00
-- url     : https://prove2.me/theorems/f462d653-0762-427b-ace8-674bd61a94e5
-- title:
--   Diagonal CP maps and commuting normal Kraus operators
-- statement:
--   On a nonzero finite space, let a diagonal CP map mean a Schur multiplier by a positive semidefinite matrix in a common orthonormal input/output basis. For every map $\Phi$,
--
--   $$\Phi\text{ is diagonal in such a basis}\quad\Longleftrightarrow\quad
--   \Phi(X)=\sum_jK_jXK_j^*\text{ for a finite commuting normal family }(K_j).$$
--
--   More generally, if $K_j$ is given by (15) using any orthonormal input basis and the canonical output basis, both families $(K_k^*K_j)_{j,k}$ and $(K_jK_k^*)_{j,k}$ consist of commuting normal operators. No converse is asserted for this broader two-basis property. Normality is essential to the first characterization.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 5, Diagonal CP maps and commuting normal Kraus operators

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- PDF p.5: normality is essential. The wider two-basis cross-product
conclusion is sufficient, with no converse asserted. -/
theorem diagonal_kraus_characterization [Nonempty A] (Phi : Superop A A) :
    (IsDiagonal Phi ↔ ∃ (r : ℕ) (E : Fin r → Matrix A A ℂ),
      Phi = krausApply E ∧ CommutingNormal E) ∧
    (∀ (U : Matrix.unitaryGroup A ℂ) (v : Matrix A B ℂ),
      let E := gramKraus v (basisColumns U)
      CommutingNormal (fun jk : B × B => (E jk.1)ᴴ * E jk.2) ∧
      CommutingNormal (fun jk : B × B => E jk.1 * (E jk.2)ᴴ)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
