-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_testingMinimax
-- name    : QAlgorithms.Papers.Independent.Information100.P69.testingMinimax
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:55:22.457364+00:00
-- url     : https://prove2.me/theorems/1efc70dd-2427-4e0c-8671-0c2c4751f64e
-- title:
--   Composite testing minimax and attainment
-- statement:
--   Let $T:H\to K$ be a channel, $\mathcal F$ a nonempty compact convex set of channels, and $0<\varepsilon<1$. Write $b_\varepsilon(T,M)$ for optimal testing against the single specified alternative $M$, and $\beta_\varepsilon(T,\mathcal F)$ for testing with one input/effect pair against the entire set. Then
--   $$\beta_\varepsilon(T,\mathcal F)=\max_{M\in\mathcal F} b_\varepsilon(T,M).$$
--   The maximum is attained, and an optimal uniform pure-input tester exists with reference isomorphic to $H$. This relates composite testing to a hardest alternative without tensor or replacer hypotheses.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 9, Lemma 5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Lemma 5, minimax, maximum attainment, and one optimal uniform tester, PDF pp.9–10. -/
theorem testingMinimax [Nonempty A] [Nonempty B] (T : Superop A B) (hT : IsChannel T) (F : Set (Superop A B))
    (hF : CompactConvexChannels F) (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    (∃ M ∈ F, simpleBeta T M eps = beta T F eps ∧
      ∀ M' ∈ F, simpleBeta T M' eps ≤ simpleBeta T M eps) ∧
    ∃ t : Tester A A B, 1-eps ≤ acceptance t T ∧ worst t F = beta T F eps := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
