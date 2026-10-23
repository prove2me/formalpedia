-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P59_crossWeightRegeneration
-- name    : QAlgorithms.Papers.Independent.Information100.P59.crossWeightRegeneration
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:27:49.13149+00:00
-- url     : https://prove2.me/theorems/27643bab-9b75-4e7d-bcd4-91f9c21c9d6b
-- title:
--   Lemma 3.15: Cross-weight regeneration by brackets
-- statement:
--   Let $E_{ij}$ denote the standard matrix units. Use the commutator bracket on real $3\times3$ matrices and $J_n v=n\times v$. Let $\mathfrak m_{1s}=\operatorname{span}\{E_{13}+E_{31},E_{23}+E_{32}\}$, $\mathfrak m_{1a}=\operatorname{span}\{J_x,J_y\}$, and $\mathfrak m_2\oplus\mathrm{dev}=\operatorname{span}\{E_{11}-E_{22},E_{12}+E_{21},\operatorname{diag}(1,1,-2)\}$. Then
--
--   $$[\mathfrak m_{1s},\mathfrak m_2\oplus\mathrm{dev}]\subseteq\mathfrak m_{1a}.$$
--
--   For each nonzero $Z$ in the second sector, there is $X\in\mathfrak m_{1s}$ with $B=[X,Z]\ne0$, and $B$ together with $[J_z,B]$ spans all of $\mathfrak m_{1a}$.
--
--   This retains nonvanishing even where the bracket pairing has rank one; the sign-sensitive supporting formulas printed in the proof are not part of this target.
-- source:
--   Lie-Wedge Stratification and Pure-State Stabilizability in Single- Channel Qubit Control, arXiv:2610.00046v1, PDF p. 15, Lemma 3.15

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P59

attribute [local instance 100] LieRing.ofAssociativeRing

/-- arXiv:2610.00046v1 PDF pp.15--16, Lemma 3.15. No sign-sensitive printed
supporting bracket formula is assumed. Nonvanishing includes the rank-one determinant-zero locus. -/
theorem crossWeightRegeneration :
    (∀ X ∈ weightOneSymmetric, ∀ Z ∈ weightTwoDeviator,
      X * Z - Z * X ∈ weightOneRotation) ∧
    (∀ Z ∈ weightTwoDeviator, Z ≠ 0 →
      ∃ X ∈ weightOneSymmetric, X * Z - Z * X ≠ 0 ∧
        Submodule.span ℝ {X * Z - Z * X,
          rotationGenerator ![0,0,1] * (X * Z - Z * X) -
            (X * Z - Z * X) * rotationGenerator ![0,0,1]} = weightOneRotation) := by sorry

end QAlgorithms.Papers.Independent.Information100.P59

end
