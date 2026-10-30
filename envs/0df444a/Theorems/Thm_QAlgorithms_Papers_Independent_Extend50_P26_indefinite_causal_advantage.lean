-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P26_indefinite_causal_advantage
-- name    : QAlgorithms.Papers.Independent.Extend50.P26.indefinite_causal_advantage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:31:34.357864+00:00
-- url     : https://prove2.me/theorems/15664072-8bae-493e-a296-f7d8d0945c3f
-- title:
--   Strict indefinite causal order advantage for two and three qubit calls
-- statement:
--   Fix $k=2$ or $k=3$. For each class let $P_{\mathcal C}(2,k)$ be the attained maximum of the success probabilities of universal heralded exact inversion of an unknown qubit operation, using $k$ forward calls to the same $U\in SU(2)$. Probabilities are constant in $U$ and the input; exactness includes reference-entangled inputs. Then
--
--   $$P_{\mathrm{adaptive}}(2,k)<P_{\mathrm{indefinite}}(2,k).$$
--
--   The adaptive class comprises arbitrary causally ordered circuits with finite memory. The indefinite class is the paper's positive process-matrix class, normalized on independently varied CPTP slot channels. Each optimum is attained by a fixed feasible success branch and deterministic completion.
--
--   This is the source's qualitative strict comparison for each budget separately. It asserts neither an exact numerical gap nor a scalable family nor physical realizability of every process matrix.
-- source:
--   Reversing Unknown Quantum Transformations: Universal Quantum Circuit for Inverting General Unitary Operations, arXiv:1810.06944v3, PDF p. 4, Paragraph following Table I; conclusions pp.4–5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P26

noncomputable section

open QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P26

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.4, paragraph following Table I, repeated in the conclusion on pp.4–5:
for each of k=2 and k=3, general processes strictly beat all ordered adaptive
circuits on the same repeated unknown qubit unitary. No numerical gap is asserted. -/
theorem indefinite_causal_advantage (k : ℕ) (hk : k = 2 ∨ k = 3) :
    ∃ a b : ℝ,
      IsGreatest {p : ℝ | Attainable .adaptive 2 k p} a ∧
      IsGreatest {p : ℝ | Attainable .indefinite 2 k p} b ∧ a < b := by sorry

end QAlgorithms.Papers.Independent.Extend50.P26

end
