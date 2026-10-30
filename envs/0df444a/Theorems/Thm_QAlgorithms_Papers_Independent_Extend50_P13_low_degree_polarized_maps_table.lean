-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_low_degree_polarized_maps_table
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.low_degree_polarized_maps_table
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:52:33.16359+00:00
-- url     : https://prove2.me/theorems/bddbc53d-8e98-4a18-8918-491d96b5e231
-- title:
--   Appendix B / Table II: explicit low-degree polarized maps
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. Put $a=\operatorname{tr}A$, $b=\operatorname{tr}B$, $c=\operatorname{tr}C$, and write $\tau(W)=\operatorname{tr}(W)$. The seven literal Table II polynomials are
--
--   $$\begin{aligned}
--   F_{11}(A)&=aI-A,\\
--   F_{21}(A,B)&=2abI-BA-AB,\\
--   F_{111}(A,B)&=(ab-\tau(BA))I-aB-bA+BA+AB,\\
--   F_{31}(A,B,C)&=[3abc+a\tau(CB)+\tau(BA)c+\tau(CA)b]I+abC+caB-\tau(BA)C-CBA-BAC-CAB-\tau(CA)B-BCA-ABC+bcA-ACB-\tau(CB)A,\\
--   F_{22}(A,B,C)&=[2abc-\tau(CBA)-\tau(BCA)]I-aCB-aBC+2\tau(BA)C-cBA-bCA+2\tau(CA)B-cAB-bAC+2\tau(CB)A,\\
--   F_{211}(A,B,C)&=[3abc-a\tau(CB)-\tau(BA)c-\tau(CA)b]I-abC-caB-\tau(BA)C+CBA+BAC+CAB-\tau(CA)B+BCA+ABC-bcA+ACB-\tau(CB)A,\\
--   F_{1111}(A,B,C)&=[abc-a\tau(CB)-\tau(BA)c+\tau(CBA)+\tau(BCA)-\tau(CA)b]I-abC+aCB+aBC-caB+\tau(BA)C-CBA-BAC+cBA-CAB+bCA+\tau(CA)B-BCA-ABC+cAB+bAC-bcA-ACB+\tau(CB)A.
--   \end{aligned}$$
--
--   For the respective partitions $(1,1),(2,1),(1,1,1),(3,1),(2,2),(2,1,1),(1,1,1,1)$, the Definition-4 normalization is
--
--   $$f_\lambda=s_\lambda F_\lambda,\qquad(s_{11},s_{21},s_{111},s_{31},s_{22},s_{211},s_{1111})=(\tfrac12,\tfrac13,\tfrac16,\tfrac18,\tfrac1{12},\tfrac18,\tfrac1{24}).$$
--
--   Each map is positive on PSD tuples, vanishes on all complex inputs whenever the number of rows exceeds $d$, is equivariant under every unitary, is completely copositive after linearizing and transposing all input factors at every positive ancillary dimension, and is tensor-stable under arbitrary finite powers with independently chosen positive local dimensions and globally PSD inputs. Empty tensor powers use the scalar algebra. These formulas make the table's suppressed positive normalization factors explicit.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 25, Appendix B / Table II: explicit low-degree polarized maps

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Appendix B, Table II (PDF pp.24–25). SOURCE NORMALIZATION: the seven printed
entries suppress their positive factors. The Definition-4 factors are respectively
1/2,1/3,1/6,1/8,1/12,1/8,1/24. All seven literal formulas and the Appendix's
positivity/vanishing/equivariance/tensor-stability/copositivity assertions are retained. -/
theorem low_degree_polarized_maps_table :
    (∀ lambda : QAlgorithms.Schur.Partition 2 2, lambda.val.rowLens = [1,1] →
      TableProperties lambda ∧ ∀ (d : ℕ), 0 < d → ∀ X : (Matrix (Fin d) (Fin d) ℂ),
        polarizedMap lambda (fun _ : Fin 1 => X) = (1/2 : ℂ) • reductionPolynomial X) ∧
    (∀ lambda : QAlgorithms.Schur.Partition 3 3, lambda.val.rowLens = [2,1] →
      TableProperties lambda ∧ ∀ (d : ℕ), 0 < d → ∀ X Y : (Matrix (Fin d) (Fin d) ℂ),
        polarizedMap lambda ![X,Y] = (1/3 : ℂ) • mixedThree X Y) ∧
    (∀ lambda : QAlgorithms.Schur.Partition 3 3, lambda.val.rowLens = [1,1,1] →
      TableProperties lambda ∧ ∀ (d : ℕ), 0 < d → ∀ X Y : (Matrix (Fin d) (Fin d) ℂ),
        polarizedMap lambda ![X,Y] = (1/6 : ℂ) • antisymmetricThree X Y) ∧
    (∀ lambda : QAlgorithms.Schur.Partition 4 4, lambda.val.rowLens = [3,1] →
      TableProperties lambda ∧ ∀ (d : ℕ), 0 < d → ∀ A B C : (Matrix (Fin d) (Fin d) ℂ),
        polarizedMap lambda ![A,B,C] = (1/8 : ℂ) • tableFour31 A B C) ∧
    (∀ lambda : QAlgorithms.Schur.Partition 4 4, lambda.val.rowLens = [2,2] →
      TableProperties lambda ∧ ∀ (d : ℕ), 0 < d → ∀ A B C : (Matrix (Fin d) (Fin d) ℂ),
        polarizedMap lambda ![A,B,C] = (1/12 : ℂ) • tableFour22 A B C) ∧
    (∀ lambda : QAlgorithms.Schur.Partition 4 4, lambda.val.rowLens = [2,1,1] →
      TableProperties lambda ∧ ∀ (d : ℕ), 0 < d → ∀ A B C : (Matrix (Fin d) (Fin d) ℂ),
        polarizedMap lambda ![A,B,C] = (1/8 : ℂ) • tableFour211 A B C) ∧
    (∀ lambda : QAlgorithms.Schur.Partition 4 4, lambda.val.rowLens = [1,1,1,1] →
      TableProperties lambda ∧ ∀ (d : ℕ), 0 < d → ∀ A B C : (Matrix (Fin d) (Fin d) ℂ),
        polarizedMap lambda ![A,B,C] = (1/24 : ℂ) • tableFour1111 A B C) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
