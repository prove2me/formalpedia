-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_graphResourceCriterion
-- name    : QAlgorithms.Papers.Independent.Information100.P22.graphResourceCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:54:22.552046+00:00
-- url     : https://prove2.me/theorems/daf92b48-e220-4aee-804e-8526d9af6bff
-- title:
--   Theorem 2: Exact graph-state resource criterion
-- statement:
--   Let $m\ge2$, $k\ge1$, and fix a graph-state representative, ordered balanced signal/key cut, sectors, and ordered distinct Pauli encoder axes. Write $A_S$ for the signal adjacency and $B$ for the binary cut matrix; let $K=\ker B^T$. Define the ambient exceptional space $E$ by Eq.(6), independently of $K$. Then
--   $$\text{exact recovery from every }S_iN\iff K\subseteq E.$$
--   The inclusion implies uniform individual concealment. Its failure implies that at least one prescribed subsystem admits no exact CPTP decoder. This makes validity depend on the entire kernel, rather than its dimension.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 7, Theorem 2: Exact graph-state resource criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Theorem 2, PDF pp.7–8, proof pp.29–31. Includes the decoder-independent failure clause. -/
theorem graphResourceCriterion (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (P Q : Axis) (hPQ : P ≠ Q) (G : CutGraph (Wires m k)) :
    (AllRecoverable (graphVector G) (twoPauliEncoder m k P Q) ↔
      (cutKernel G : Set _) ⊆ exceptionalSpace P Q G.AS) ∧
    (((cutKernel G : Set _) ⊆ exceptionalSpace P Q G.AS) →
      UniformlyConcealed (graphVector G) (twoPauliEncoder m k P Q)) ∧
    (¬ ((cutKernel G : Set _) ⊆ exceptionalSpace P Q G.AS) →
      ∃ i, ¬ Recoverable (graphVector G) (twoPauliEncoder m k P Q) i) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
