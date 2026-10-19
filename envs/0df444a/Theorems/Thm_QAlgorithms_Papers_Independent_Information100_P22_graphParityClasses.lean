-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_graphParityClasses
-- name    : QAlgorithms.Papers.Independent.Information100.P22.graphParityClasses
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:55:58.114276+00:00
-- url     : https://prove2.me/theorems/76d7f7f3-faee-47eb-a7bf-053a856b738e
-- title:
--   Corollary 4: Parity- and encoder-dependent graph-state classes
-- statement:
--   For a fixed graph realization and ordered distinct encoder axes, let $K=\ker B^T$, $r=\operatorname{rank}_{\mathbb F_2}B$, and $\nu=mk$, where $m\ge2$, $k\ge1$. Let $F(c)=(c_j\mathbf1_m)_j$, $E_Y=\{Fc:(A_S+I)Fc=0,\sum_jc_j=0\}$ and $E_X=\{Fc:A_SFc=0\}$. Exact recovery holds precisely when
--   $$\begin{cases}K=0,&m\text{ even},\\K\subseteq E_Y,&m\text{ odd, XZ/ZX},\\K\subseteq E_X,&m\text{ odd, YZ/ZY},\\K=0,&m\text{ odd, XY/YX}.\end{cases}$$
--   Consequently valid resources have respectively $r=mk$, $r\ge mk-k+1$, $r\ge(m-1)k$, and $r=mk$. The exceptional rank bounds are only necessary; the inclusions remain the exact test. This separates rank from kernel orientation.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 8, Corollary 4: Parity- and encoder-dependent graph-state classes

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Corollary 4, PDF pp.8–9: exact branch inclusions, followed by necessary rank consequences. -/
theorem graphParityClasses (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (P Q : Axis) (hPQ : P ≠ Q) (G : CutGraph (Wires m k)) :
    (AllRecoverable (graphVector G) (twoPauliEncoder m k P Q) ↔
      if Even m then cutKernel G = ⊥ else
      if classXZ P Q then (cutKernel G : Set _) ⊆ exceptionalY G.AS else
      if classYZ P Q then (cutKernel G : Set _) ⊆ exceptionalX G.AS else cutKernel G = ⊥) ∧
    (AllRecoverable (graphVector G) (twoPauliEncoder m k P Q) →
      ((Even m ∨ (Odd m ∧ classXY P Q)) → G.B.rank = m*k) ∧
      ((Odd m ∧ classXZ P Q) → m*k-k+1 ≤ G.B.rank) ∧
      ((Odd m ∧ classYZ P Q) → (m-1)*k ≤ G.B.rank)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
