-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_catRedistribution
-- name    : QAlgorithms.Papers.Independent.Gap48.P20.catRedistribution
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:07:03.976648+00:00
-- url     : https://prove2.me/theorems/092bd3bf-7c17-4955-a367-83ae8c4d578e
-- title:
--   Exact local redistribution of the four-party cat state
-- statement:
--   Consider four qubits in the normalized cat state
--   $$
--   |\mathrm{cat}\rangle^{ACBR}=\frac{|0000\rangle+|1111\rangle}{\sqrt2}.
--   $$
--   Alice holds $AC$ and Bob holds $B$. On the source support Alice maps $|zz\rangle^{AC}$ to $|z\rangle^A$, and Bob applies $|z\rangle^B\mapsto|zz\rangle^{CB}$, for $z\in\{0,1\}$. A complete trace-preserving extension of Alice's map has Kraus operators $K_w|a,c\rangle=\mathbf 1_{\{w=a\mathbin{\oplus}c\}}|a\rangle$; it is CNOT from $A$ to $C$ followed by discarding $C$. Bob's map is an isometry on his entire input space.
--
--   These two local channels exactly reproduce the original coherent cat state with $C$ now at Bob and $R$ untouched, without any communication or Bell resources. The optimal asymptotic corner is
--   $$
--   Q_*=E_*=0.
--   $$
--   This example illustrates redistribution using correlations already present in the source. Alice's printed support map is not asserted to be an isometry on the full four-dimensional space.
-- source:
--   The operational meaning of quantum conditional information, arXiv:quant-ph/0612050v2, PDF p. 3, cat-state

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P20

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, application (1): complete zero-message local implementation and the
zero optimal rate pair. Alice's printed 4-to-2 map is used only on its support;
catAlice supplies its trace-preserving extension on the orthogonal complement. -/
theorem catRedistribution :
    IsState catState ∧ IsChannel catAlice ∧ IsChannel catBob ∧
    idTensorSuperop (localProduct catAlice catBob) catInput = pureDensity catState ∧
    quantumCost catState = 0 ∧ redistributionEntanglementRate catState = 0 ∧
    RedistributionAchievable catState 0 0 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P20

end
