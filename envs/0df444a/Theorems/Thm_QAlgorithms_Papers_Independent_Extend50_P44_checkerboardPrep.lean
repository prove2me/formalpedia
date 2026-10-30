-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_checkerboardPrep
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.checkerboardPrep
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:16:21.88273+00:00
-- url     : https://prove2.me/theorems/7447ba55-597b-403a-8727-556db4fbc075
-- title:
--   §3.1: checkerboard PREP circuit (45)–(47)
-- statement:
--   Let $n\ge1$, $N=2^n$, and $A_{ij}=a_{(i+j)\bmod2}$ for real values not both zero. Fix the checkerboard label scheme and its data-preserving tensor factors before choosing the values. Signed normalized PREP and UNPREP operators at $p=1/2$ can be chosen so that circuit (45), without a deletion flag, satisfies
--   $$ (\langle0|\otimes I)U(|0\rangle\otimes I)=A/\alpha,\qquad\alpha=\frac N2(|a_0|+|a_1|)\le N\max(|a_0|,|a_1|). $$
--   The preparation convention is (29)-(30), which also covers negative values; no square root of a negative data item is used. This improves the checkerboard base normalization.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 13, §3.1: checkerboard PREP circuit (45)–(47)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF p.13, (45)-(47): signed PREP/UNPREP checkerboard construction.
The two normalized preparation operators use the general sign conventions,
rather than taking square roots of negative entries in the printed (46). -/
theorem checkerboardPrep (n : ℕ) (hn : 1 ≤ n) :
    ∃ B : Scheme n n 1 (2 * n - 1), ∃ L : PrepLayout B,
      CheckerLabels B ∧ L.active = Finset.univ ∧
      ∀ a : Fin 2 → ℝ, 0 < tableMax a →
      ∃ P : PreparationPair L a (1 / 2), B.matrix a = checkerboard n a ∧
        QAlgorithms.IsBlockEncoding (0 : Fin (2 ^ n)) (L.noDeleteCircuit P)
          ((2 ^ n : ℕ) * (|a 0| + |a 1|) / 2) 0 (checkerboard n a) ∧
        ((2 ^ n : ℕ) : ℝ) * (|a 0| + |a 1|) / 2 ≤
          (2 ^ n : ℕ) * max |a 0| |a 1| := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
