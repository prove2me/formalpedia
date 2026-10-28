-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_depolarizingBasisShannonOptimum
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.depolarizingBasisShannonOptimum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:57:15.602761+00:00
-- url     : https://prove2.me/theorems/69f71dd4-cffb-4ee5-8706-359d3bede82b
-- title:
--   Uniform basis ensemble and same-basis measurement attain Shannon capacity
-- statement:
--   Let $d\ge2$ and $-1/(d^2-1)\le\lambda\le1$. Write $\Delta_\lambda(X)=\lambda X+(1-\lambda)\operatorname{Tr}(X)I/d$. All states are positive semidefinite with trace one; all information quantities use natural logarithms with $0\log0=0$. Let $C_{\rm Shan}$ be the supremum of mutual information over all finite normalized input ensembles and finite output POVMs, and let $\chi^*$ be the supremum of output Holevo information. Then
--
--   $$C_{\rm Shan}(\Delta_\lambda)=\chi^*(\Delta_\lambda).$$
--
--   For every orthonormal basis $(u_i)_{i=1}^d$, the ensemble $\{(1/d,|u_i\rangle\langle u_i|)\}$ consists of density matrices and its same-basis projectors form a POVM. The mutual information of this specific ensemble and measurement equals $C_{\rm Shan}$. This supplies an attaining measurement as well as an equality of suprema.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 6, Unnumbered result (17): the one-use Shannon optimum is a basis ensemble and measurement

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

namespace QAlgorithms.Papers.Independent.Gap48.P03

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten block)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P43 (ordinaryLimit)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- King quant-ph/0204172v2, PDF p.6, (17): the same arbitrary orthonormal
basis for uniform encoding and projective measurement attains the Shannon supremum. -/
theorem depolarizingBasisShannonOptimum {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ)^2 - 1) ≤ lam) (hhigh : lam ≤ 1) :
    quantumShannonCapacity (depolarizing d (1 - lam)) = holevoQuantity (depolarizing d (1 - lam)) ∧
    ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      IsLaw (basisProb d) ∧
      (∀ k, IsDensityMatrix (basisProjector (U : Matrix (Fin d) (Fin d) ℂ) k)) ∧
      IsPOVM (basisProjector (U : Matrix (Fin d) (Fin d) ℂ)) ∧
      measuredInformation (depolarizing d (1 - lam)) (basisProb d)
        (basisProjector (U : Matrix (Fin d) (Fin d) ℂ))
        (basisProjector (U : Matrix (Fin d) (Fin d) ℂ)) =
        quantumShannonCapacity (depolarizing d (1 - lam)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
