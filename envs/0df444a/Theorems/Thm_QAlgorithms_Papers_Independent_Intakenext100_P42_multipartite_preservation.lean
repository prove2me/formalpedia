-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_multipartite_preservation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.multipartite_preservation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:55:03.88714+00:00
-- url     : https://prove2.me/theorems/08cdc031-1cb8-4302-92a5-71647f6cb6c8
-- title:
--   Unnumbered Eq.(93): preservation of Eq.(91) class
-- statement:
--   Let $N\ge3$ parties have arbitrary positive finite dimensions. A state is biseparable if it is a finite convex mixture of products of density matrices across nonempty proper bipartitions, permitting entanglement inside blocks and mixtures across cuts. Let $V_k=\bigotimes_{j=1}^NA_{k,j}$ be a finite complete family, $\sum_kV_k^\dagger V_k=I$. Then
--
--   $$\rho\ \mathrm{biseparable}\quad\Longrightarrow\quad\sum_kV_k\rho V_k^\dagger\ \mathrm{biseparable}.$$
--
--   For four parties this includes every 1:3 and 2:2 cut, preserving Eq.(91) rather than the fully separable alternative (94).
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 34, Unnumbered Eq.(93): preservation of Eq.(91) class

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P42

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P42

open QAlgorithms QAlgorithms.Entanglement

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.34–35, Eqs.(91)–(93): local product Kraus maps preserve mixtures across
all nontrivial cuts, for arbitrary party count and positive local dimensions. -/
theorem multipartite_preservation {N r : ℕ} (hN : 3 ≤ N) (d : Fin N → ℕ)
    (hd : ∀ i, 0 < d i)
    (A : Fin r → ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hcomplete : IsKrausFamily (fun k => partyKraus (A k)))
    (rho : Matrix (∀ i, Fin (d i)) (∀ i, Fin (d i)) ℂ) (hrho : IsMultipartiteBiseparable d rho) :
    IsMultipartiteBiseparable d (krausApply (fun k => partyKraus (A k)) rho) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
