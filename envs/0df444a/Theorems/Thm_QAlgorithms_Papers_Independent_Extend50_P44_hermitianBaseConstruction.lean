-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_hermitianBaseConstruction
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.hermitianBaseConstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:13:59.267726+00:00
-- url     : https://prove2.me/theorems/0bfd5fa1-2d62-43ba-bb5f-aeed8350f0c9
-- title:
--   §2.4: Hermitian base construction (35)–(36)
-- statement:
--   Fix a compatible base scheme and a transpose permutation $T$ on every physical label. Assume $T^2=I$, $T$ preserves the data label and range predicate, the row oracle is the column oracle composed with $T$, and the two sparsity preparations coincide. For real supplied data with $M_a>0$, prepend Z to the data-flag RX rotation as in (36). Then
--   $$ U^\dagger=U,\qquad(\langle0|\otimes I)U(|0\rangle\otimes I)=A/(\sqrt{S_cS_r}M_a). $$
--   The circuit retains one loading of $D$ items and $s+2$ physical flags. Hermiticity is a conclusion about the full unitary, including invalid-label completions.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 11, §2.4: Hermitian base construction (35)–(36)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF p.11, (35)-(36): RX preceded by Z, transpose, and range deletion
produce a Hermitian full unitary with the base resources. -/
theorem hermitianBaseConstruction (B : Scheme n s d m) (T : TransposeOracle B)
    (a : Fin (2 ^ d) → ℝ) (active : Finset (Fin (2 ^ d))) (hactive : active.Nonempty)
    (hpadding : ∀ j, j ∉ active → a j = 0)
    (ha : 0 < tableMax a) :
    QAlgorithms.IsBlockEncoding ((false, false), 0) (B.baseCircuit a true)
      (B.baseAlpha a) 0 (B.matrix a) ∧
    (B.baseCircuit a true)ᴴ = B.baseCircuit a true ∧
    loadingCost (baseLoadingSchedule active.card) = active.card ∧
    Fintype.card ((Bool × Bool) × Fin (2 ^ s)) = 2 ^ (s + 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
