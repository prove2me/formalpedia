-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_prepConstruction
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.prepConstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:11:55.87902+00:00
-- url     : https://prove2.me/theorems/b34dc14f-aee7-40b4-87bb-693a0af306e3
-- title:
--   §2.3: PREP/UNPREP block encoding (28)–(32)
-- statement:
--   Fix a padded row/column scheme whose full arithmetic maps preserve the data label. Assume the physical sparsity register factors compatibly into a data register and a residual register on each side, with supports of cardinalities $S_c=D R_c$ and $S_r=D R_r$. The $D>0$ active real values $a_j$ are nonzero and all other table slots are fixed zero. For $p\in[0,1]$, normalized PREP and UNPREP completions with amplitudes (29)-(30) exist. Circuit (31) is unitary and block encodes $A$ with
--   $$ \alpha_p=\frac{\sqrt{S_cS_r}}{D}\sqrt{\left(\sum_j|a_j|^{2p}\right)\left(\sum_j|a_j|^{2-2p}\right)}. $$
--   It loads $2D$ items and uses one deletion flag plus the physical preparation/sparsity bit width. This is the complete normalization from (32), including its prefactor.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 10, §2.3: PREP/UNPREP block encoding (28)–(32)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF pp.10-11, (28)-(32): exact PREP/UNPREP construction for compatible
register factors and commuting arithmetic oracles; two independent preparations
load 2D items. No repeated amplification is included. -/
theorem prepConstruction (B : Scheme n s d m) (L : PrepLayout B)
    (a : Fin (2 ^ d) → ℝ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hnz : ∀ j ∈ L.active, a j ≠ 0)
    (hzero : ∀ j, j ∉ L.active → a j = 0) :
    ∃ P : PreparationPair L a p, QAlgorithms.IsBlockEncoding (false, 0) (L.circuit P) (L.alpha a p) 0 (B.matrix a) ∧
    loadingCost (doubleLoadingSchedule L.active.card) = 2 * L.active.card ∧
    Fintype.card (Bool × Fin (2 ^ s)) = 2 ^ (s + 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
