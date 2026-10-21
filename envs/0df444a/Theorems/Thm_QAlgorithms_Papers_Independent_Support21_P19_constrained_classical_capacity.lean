-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_constrained_classical_capacity
-- name    : QAlgorithms.Papers.Independent.Support21.P19.constrained_classical_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T05:11:24.122989+00:00
-- url     : https://prove2.me/theorems/824e3e92-d6f3-41f2-bcfc-85b1123d469f
-- title:
--   Proposition 5: entanglement-constrained classical capacity of a unitary
-- statement:
--   Let $U$ be a finite-dimensional bipartite unitary gate and $e\in\mathbb R$. Define $C_e(U)$ as the extended-real supremum of achievable nonnegative forward classical communication rates per call of $U$ with net entanglement budget $e$. Negative $e$ requires production of $-e$ ebits per use. Then
--
--   $$
--   C_e(U)=\Delta\chi_e(U):=\sup_{\mathcal E}\left\{\chi(U\mathcal E)-\chi(\mathcal E):E(\mathcal E)-E(U\mathcal E)\le e\right\}.
--   $$
--
--   The supremum ranges over every finite ensemble of normalized bipartite pure states, every finite label set, and arbitrary finite local ancillas on which $U$ acts as identity. For each ensemble, $E$ is average entanglement entropy and $\chi$ is Bob's Holevo information in bits. Both suprema are extended-real; an empty feasible set has value $-\infty$. No maximizing ensemble or dimension bound is assumed. This gives the entanglement-constrained operational capacity by a one-use entropy optimization.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 4, Proposition 5: entanglement-constrained classical capacity of a unitary

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Proposition 5: operational classical capacity equals the constrained one-use
Holevo gain for every real net entanglement budget, including infeasible negative budgets. -/
theorem constrained_classical_capacity (U : Resource) (hU : IsUnitaryResource U) (e : ℝ) :
    CapacityC U e=DeltaChi U e := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
