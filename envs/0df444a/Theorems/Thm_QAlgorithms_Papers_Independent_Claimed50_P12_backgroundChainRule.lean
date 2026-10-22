-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_backgroundChainRule
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.backgroundChainRule
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:36:43.154981+00:00
-- url     : https://prove2.me/theorems/3034dbbb-63ea-4f7c-b386-4f76b3919ca4
-- title:
--   Conditional mutual information chain rule
-- statement:
--   Let $A_1,\ldots,A_n,B,C$ be arbitrary nonzero finite-dimensional systems and $\rho$ a density operator on their tensor product. Then
--
--   $$I(A_1\cdots A_n:C|B)_\rho=\sum_{i=1}^n I(A_i:C|BA_1\cdots A_{i-1})_\rho.$$
--
--   Each term is computed from the appropriate prefix marginal and its four finite von Neumann entropies in bits. The systems $A_i$ may have different dimensions. At $n=0$ the sum is empty and both sides vanish.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 1, BackgroundChainRule

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- CMI chain rule (PDF p.1), for all heterogeneous finite families.
The ith summand is I(A_i:C|B A_<i), expanded into its four marginal entropies. -/
theorem backgroundChainRule {n : ℕ} {H : Fin n → Type*} {B C : Type*}
    [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)] [∀ i, Nonempty (H i)]
    [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C] [Nonempty B] [Nonempty C]
    (rho : Op (((i : Fin n) → H i) × (B × C))) (hrho : IsDensityMatrix rho) :
    cmi rho = ∑ i : Fin n,
      (vnEntropy (marginalAB (prefixMarginal rho (i.val+1))) +
        vnEntropy (prefixMarginal rho i.val) -
        vnEntropy (marginalAB (prefixMarginal rho i.val)) -
        vnEntropy (prefixMarginal rho (i.val+1))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
