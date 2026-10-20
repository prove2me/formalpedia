-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P12_bellHashingSplit
-- name    : QAlgorithms.Papers.Independent.Frontier30.P12.bellHashingSplit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:11:43.913926+00:00
-- url     : https://prove2.me/theorems/5cb4145a-a967-4954-883f-4c69fc211f45
-- title:
--   Example 12: Bell-mixture communication split
-- statement:
--   Let $(p_{ij})_{i,j\in\{0,1\}}$ be nonnegative with sum one. Set $\rho=\sum_{i,j}p_{ij}\Phi_{ij}$, where $\Phi_{00}=\Phi^+$, $\Phi_{01}=\Phi^-$, $\Phi_{10}=\Psi^+$ and $\Phi_{11}=\Psi^-$. Use the normalized purification $|\psi\rangle=\sum_{i,j}\sqrt{p_{ij}}|\Phi_{ij}\rangle|ij\rangle_E$, and let $X$ be Alice's computational outcome, which is uniform on $\{0,1\}$. Put $q_i=p_{i0}+p_{i1}$. Then
--
--   $$I(A:E)_\psi=I(B:E)_\psi=H(p),\qquad H(X)-I(X;B)=H(q),\qquad I(X;E)=H(p)-H(q).$$
--
--   All entropies use base two. These identities allow zero weights. If $H(p)<1$, there is one evaluated one-way EPR protocol sequence with rate $1-H(p)$ and two public message components, whose per-copy logarithmic alphabet sizes tend respectively to $H(q)$ and $H(p)-H(q)$. Their product is the protocol's total message alphabet, so the total cost tends to $H(p)$.
--
--   This identifies the code-information and phase-information parts of the construction. The purification uses the first, normalized Bell sum on p.8, avoiding the subsequent printed Schmidt normalization typo.
-- source:
--   Distillation of secret key and entanglement from quantum states, arXiv:quant-ph/0306078v1, PDF p. 8, Example 12

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- arXiv:quant-ph/0306078v1, PDF pp.8--9, Example 12. Entropy identities
include zero weights. Only the positive-yield protocol requires H(p)<1.
The normalized Bell-sum purification avoids the printed 1/sqrt(1) typo. -/
theorem bellHashingSplit (p : Bool × Bool → ℝ) (hp : IsLaw p) :
    mutualAE (QAlgorithms.pureDensity (bellPurification p)) = shannon p ∧
    quantumMutualInfo (QAlgorithms.traceLeft
      (QAlgorithms.pureDensity (bellPurification p))) = shannon p ∧
    shannon (fun _ : Bool => (1/2 : ℝ)) -
      labelInformation (fun _ : Bool => (1/2 : ℝ))
        (fun x => QAlgorithms.traceRight (bellConditional p x)) = shannon (bellBitLaw p) ∧
    labelInformation (fun _ : Bool => (1/2 : ℝ))
      (fun x => QAlgorithms.traceLeft (bellConditional p x)) =
        shannon p - shannon (bellBitLaw p) ∧
    (shannon p < 1 → EntSplitAttains (bellDiagonalState p) (1 - shannon p)
      (shannon (bellBitLaw p)) (shannon p - shannon (bellBitLaw p))) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P12

end
