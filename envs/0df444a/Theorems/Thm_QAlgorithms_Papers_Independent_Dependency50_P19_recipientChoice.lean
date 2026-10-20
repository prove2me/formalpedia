-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_recipientChoice
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.recipientChoice
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:21:16.057583+00:00
-- url     : https://prove2.me/theorems/ae4cf01c-e9ae-4965-88ec-c98de5eca4e7
-- title:
--   One random FQSW encoder works for either recipient
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Fix a pure state $\psi^{XY}$. Alice holds $X_1X_2$, Rebecca holds $Y_1$, and Bob holds $Y_2$, in $n$ independent copies of $\psi^{X_1Y_1}\otimes\psi^{X_2Y_2}$. For every $\epsilon,\delta>0$ and failure tolerance $\eta\in(0,1)$, every sufficiently large $n$ admits a fixed local compression $S$ followed by a Haar-random unitary $U$ on retained $L$ and communicated $Q$, with
--
--   $$\log_2 d_Q\le n(H(X)_\psi+\delta),\qquad \log_2 d_L\ge n(H(X)_\psi-\delta).$$
--
--   There is a measurable event of unitaries with probability at least $1-\eta$ such that the very same encoder $US$ works for both recipient choices. For each choice a recipient-local CPTP decoder gives the corresponding complete transferred-source tensor EPR target within full trace norm $\epsilon$. The encoder, message subsystem, and good event are chosen before the recipient; only the decoder may depend on that choice.
--
--   This expresses the common subsystem carrying either form of entanglement.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 20, Section XII, pp.20–21

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section XII, PDF pp.20–21: the same random encoder works for either recipient
with arbitrarily high probability. Encoder and good event precede recipient choice. -/
theorem recipientChoice {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Nonempty X] [Nonempty Y]
    (psi : EuclideanSpace ℂ (X × Y)) (hpsi : IsState psi) :
    ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∀ eta > (0 : ℝ), eta < 1 →
    ∃ N : ℕ, ∀ n ≥ N, ∃ l q : ℕ, 0 < l ∧ 0 < q ∧
      Real.logb 2 q ≤ n*(vnEntropy (traceRight (pureDensity psi))+delta) ∧
      n*(vnEntropy (traceRight (pureDensity psi))-delta) ≤ Real.logb 2 l ∧
      ∃ S : Superop (Fin n → X × X) (Fin (l*q)), IsChannel S ∧
      ∃ Good : Set (Matrix.unitaryGroup (Fin (l*q)) ℂ), MeasurableSet Good ∧
        ENNReal.ofReal (1-eta) ≤ Schur.unitaryHaar (l*q) Good ∧
        ∀ U ∈ Good, RecipientGood psi n l q (randomizedEncoder l q S U) eps := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
