-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_higher_local_commutant
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.higher_local_commutant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:19:55.804803+00:00
-- url     : https://prove2.me/theorems/1a7ae494-588f-40e2-bf95-e958718c603f
-- title:
--   Eq.(39): higher-copy local symmetries
-- statement:
--   Let $L=\bigotimes_{j=1}^n U(2)$ denote the represented local unitary group. Let $n\ge0$ and $k\ge1$. For each site $j$, independently choose a permutation $\pi_j\in S_k$, and let $P_{(\pi_j)}$ permute the $k$ copies of that site's qubit in the physical tensor representation. Then
--
--   $$C^{(k)}(L)=\operatorname{span}_{\mathbb C}\{P_{(\pi_j)}:(\pi_j)\in S_k^n\}.$$
--
--   This is a spanning identity. It retains the representation kernel and makes no assertion that the $(k!)^n$ displayed operators are linearly independent.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 14, Eq.(39): higher-copy local symmetries

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.14, Eq.(39): physical local permutations span the higher-copy
tensorCommutant. No linear independence or factorial dimension is asserted. -/
theorem higher_local_commutant (n k : ℕ) (hk : 0 < k) :
    tensorCommutant k (localUnitaryMatrices n) =
      (Submodule.span ℂ (Set.range (localPermutation n k)) :
        Set (Mat (Copies (Qubits n) k))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
