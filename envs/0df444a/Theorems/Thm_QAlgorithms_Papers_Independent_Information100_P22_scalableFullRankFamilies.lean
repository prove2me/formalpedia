-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_scalableFullRankFamilies
-- name    : QAlgorithms.Papers.Independent.Information100.P22.scalableFullRankFamilies
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:05:03.608957+00:00
-- url     : https://prove2.me/theorems/b6e73961-4cfe-46a6-ab0d-3dd8936dca40
-- title:
--   Proposition S1: Scalable full-rank graph families
-- statement:
--   Let $\nu\ge2$. Perfect matchings, $P_{2\nu}$, $C_{2\nu}$, and rectangular clusters with $2a$ rows and $b$ columns, $a,b\ge1$ and $ab=\nu$, admit ordered balanced cuts satisfying
--   $$\operatorname{rank}_{\mathbb F_2}B=\nu.$$
--   For each factorization $\nu=mk$ with $m\ge2$, $k\ge1$, each family therefore admits sectors and a cut supporting every ordered distinct two-Pauli encoder, exact recovery from all $S_iN$, and uniform individual concealment. This supplies scalable fully entangled graph resources.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 38, Proposition S1: Scalable full-rank graph families

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Proposition S1, PDF pp.38–39. Every named scalable family admits full-rank cuts and all factorizations. -/
theorem scalableFullRankFamilies (nu : ℕ) (hnu : 2 ≤ nu) (G : LabeledGraph (Fin (2*nu)))
    (hfamily : G = matchingGraph nu ∨ G = pathGraph nu ∨ G = cycleGraph nu ∨
      ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ a*b = nu ∧ G = rectangularGraph nu b) :
    (∃ e : (Fin nu ⊕ Fin nu) ≃ Fin (2*nu),
      (Matrix.of fun a b : Fin nu => G.adj (e (.inl a)) (e (.inr b))).rank = nu) ∧
    (∀ m k : ℕ, 2 ≤ m → 1 ≤ k → m*k = nu →
      ∃ e : (Wires m k ⊕ Wires m k) ≃ Fin (2*nu),
        (realize G e).B.rank = nu ∧ ∀ P Q : Axis, P ≠ Q →
          AllRecoverable (graphVector (realize G e)) (twoPauliEncoder m k P Q) ∧
          UniformlyConcealed (graphVector (realize G e)) (twoPauliEncoder m k P Q)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
