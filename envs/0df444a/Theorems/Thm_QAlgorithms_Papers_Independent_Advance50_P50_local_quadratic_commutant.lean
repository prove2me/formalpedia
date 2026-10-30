-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_local_quadratic_commutant
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.local_quadratic_commutant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:14:59.157322+00:00
-- url     : https://prove2.me/theorems/91953ac0-ed81-40e1-ae21-8ac3bb1b5f20
-- title:
--   Eq.(33): local quadratic symmetry algebra
-- statement:
--   Let $L=\bigotimes_{j=1}^n U(2)$ denote the represented local unitary group. Fix $n\ge0$, and let $S_Q$ swap the two copies at precisely the sites in $Q\subseteq S=\{1,\ldots,n\}$. Then
--
--   $$C^{(2)}(L)=\operatorname{span}_{\mathbb C}\{S_Q:Q\subseteq S\}.$$
--
--   Copy-major indices are explicitly transposed into paired-site indices in each generator. This identifies the physical quadratic symmetry algebra and includes the identity at $Q=\varnothing$.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 13, Eq.(33): local quadratic symmetry algebra

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

/-- PDF p.13, Eq.(33): the complex quadratic tensorCommutant is spanned by the
2^n physical products of site swaps and site identities. -/
theorem local_quadratic_commutant (n : ℕ) :
    tensorCommutant 2 (localUnitaryMatrices n) =
      (Submodule.span ℂ (Set.range (fun Q : Finset (Fin n) => subsystemSwap Q)) :
        Set (Mat (Copies (Qubits n) 2))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
