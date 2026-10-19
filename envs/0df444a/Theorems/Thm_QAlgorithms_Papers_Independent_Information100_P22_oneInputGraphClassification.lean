-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_oneInputGraphClassification
-- name    : QAlgorithms.Papers.Independent.Information100.P22.oneInputGraphClassification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:57:10.60649+00:00
-- url     : https://prove2.me/theorems/da45ad46-fcfc-4b49-ba08-e1e1d9e21f34
-- title:
--   Corollary 5: Single-input-qubit classification
-- statement:
--   Let $k=1$, $m\ge2$, in the fixed graph-state Pauli frame. For the XZ/ZX and XY/YX encoder classes, and for even $m$ also YZ/ZY, validity is equivalent to $\operatorname{rank}B=m$. For odd $m$ in the YZ/ZY class,
--   $$\text{valid}\iff K=0\ \text{or}\ [K=\operatorname{span}\{\mathbf1_m\}\text{ and }A_S\mathbf1_m=0].$$
--   All ranks and spans are over $\mathbb F_2$. This identifies the only rank-deficient single-input branch.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 8, Corollary 5: Single-input-qubit classification

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Corollary 5, PDF pp.8–9,32: the exceptional rank-deficient single-input branch. -/
theorem oneInputGraphClassification (m : ℕ) (hm : 2 ≤ m) (P Q : Axis) (hPQ : P ≠ Q)
    (G : CutGraph (Wires m 1)) :
    (AllRecoverable (graphVector G) (twoPauliEncoder m 1 P Q) ↔
      if Odd m ∧ classYZ P Q then
        cutKernel G = ⊥ ∨ (cutKernel G = Submodule.span F2 {fun _ => (1 : F2)} ∧
          G.AS.mulVec (fun _ => 1) = 0)
      else G.B.rank = m) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
