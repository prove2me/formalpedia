-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_depolarizing_superadditivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.depolarizing_superadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:53:02.72967+00:00
-- url     : https://prove2.me/theorems/3fe89716-0402-40b0-8ed1-4a6b1d629124
-- title:
--   §5: strong-superadditivity instances from depolarizing dilation subspaces
-- statement:
--   Let $n\ge1$. For each $i=1,\ldots,n$ take an Example 6 depolarizing dilation with dimension $d_i\ge2$, parameter $-1/(d_i^2-1)\le\lambda_i\le1$, identity-containing orthogonal unitary error basis, and actual Kraus-block range $K_{\lambda_i}$. The error basis obeys $\operatorname{Tr}(\sigma_{i,j}^\dagger\sigma_{i,k})=d_i\delta_{jk}$; the weights are $p_{i,0}=\lambda_i+(1-\lambda_i)/d_i^2$ and $p_{i,j}=(1-p_{i,0})/(d_i^2-1)$ for $j>0$. Let $\psi$ be any unit vector in $\bigotimes_i K_{\lambda_i}$ and let $\rho_i$ be its actual marginal on the $i$th output-environment pair. Put $a_i=\lambda_i+(1-\lambda_i)/d_i$, $b_i=(1-\lambda_i)/d_i$ and $h_i=-a_i\log_2a_i-(d_i-1)b_i\log_2b_i$. Then
--   $$E(\psi)\ge\sum_{i=1}^n h_i=\sum_{i=1}^n E_f(\rho_i).$$
--   The entanglement of the joint vector uses the cut of all outputs versus all environments. This is a special strong-superadditivity family, using King's cited minimum-output-entropy additivity result [21], rather than an assertion of the general conjecture.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 8, §5: strong-superadditivity instances from depolarizing dilation subspaces

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P60

namespace QAlgorithms.Papers.Independent.Intakenext100.P60

open scoped Matrix ComplexConjugate ComplexOrder TensorProduct

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix, normalized ensemble, convex roof, grouped copies and LOCC.

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble pureAverage formation)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open QAlgorithms.Papers.Independent.Gap48.P32 (twoWayDistillable)

/-- PDF p.8: strong superadditivity for pure states in a tensor product of the actual
Example 6 subspaces. King [21] supplies the cited minimum-output-entropy additivity input.
The middle sum is the explicit Smin spectrum from p.10; local marginals are constructed. -/
theorem depolarizing_superadditivity {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ)
    (D : ∀ i, DepolarizingData (d i))
    (psi : EuclideanSpace ℂ ((∀ i, Fin (d i)) × (∀ i, Fin (d i ^ 2))))
    (hpsi : ‖psi‖ = 1)
    (hsupport : (fun q => psi q) ∈ dilationSpace (jointDepolarizing D)) :
    (∑ i, depolarizingEntropyBits (D i)) ≤ pureEntropyBits psi ∧
      (∑ i, depolarizingEntropyBits (D i)) =
        ∑ i, formation (pairMarginal (pureDensity psi) i) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
