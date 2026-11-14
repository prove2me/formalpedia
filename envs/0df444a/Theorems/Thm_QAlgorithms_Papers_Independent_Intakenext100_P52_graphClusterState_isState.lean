-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_graphClusterState_isState
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.graphClusterState_isState
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T04:10:35.790006+00:00
-- url     : https://prove2.me/theorems/9b3c8c1d-4660-4d81-835b-abb5ccf9ab35
-- title:
--   Every finite graph cluster ket has unit norm
-- statement:
--   Let $V$ be a finite set of qubit sites, let $E\subseteq V\times V$ be a finite set of ordered edges, and write $\epsilon_E(z)=\prod_{(u,v)\in E}(-1)^{z_u z_v}$ for a computational bit string $z$. The graph cluster ket
--
--   $$|C_E\rangle=2^{-|V|/2}\sum_{z\in\{0,1\}^V}\epsilon_E(z)|z\rangle$$
--
--   has norm one. The conclusion also holds for the empty site set and requires no connectedness condition. It certifies normalization for graph-state measurement and valence-bond projection formulas.
-- source:
--   R. Jozsa, An introduction to measurement based quantum computation, https://arxiv.org/abs/quant-ph/0508124v2, PDF pp.8,11–12, cluster-state preparation by CZ edges; finite-graph normalization of that construction.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Intakenext100.P52 QAlgorithms.Papers.Independent.Information100.P21 QAlgorithms.Papers.Independent.Gap20.P01
open scoped Matrix ComplexConjugate
private theorem edgePhase_norm {V : Type*} [DecidableEq V] (E : Finset (V × V)) (z : V → Bool) :
    ‖edgePhase E z‖ = 1 := by
  simp only [edgePhase, norm_prod]
  apply Finset.prod_eq_one
  intro e he
  cases z e.1 <;> cases z e.2 <;> simp [czPhase]

theorem QAlgorithms.Papers.Independent.Intakenext100.P52.graphClusterState_isState {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) : IsState (graphClusterState E) := by sorry
