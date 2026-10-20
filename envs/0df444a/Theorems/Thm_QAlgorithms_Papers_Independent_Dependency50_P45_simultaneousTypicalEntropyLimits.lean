-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P45_simultaneousTypicalEntropyLimits
-- name    : QAlgorithms.Papers.Independent.Dependency50.P45.simultaneousTypicalEntropyLimits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:01:41.565987+00:00
-- url     : https://prove2.me/theorems/3dbf6147-cdf0-457a-98ab-404197dae92f
-- title:
--   Lemma 1, both statements: simultaneous frequency-typical output entropy limits
-- statement:
--   Let $\rho$ be a density matrix on a nonzero finite-dimensional complex space $A$, and let $\mathcal N:A\to B$ and $\mathcal F:A\to E$ be any two CPTP maps with finite nonzero outputs. Fix any orthonormal eigenbasis of $\rho$, with eigenvalues $\lambda_a\ge0$ summing to one. A supported word of length $n$ uses only positive-eigenvalue directions and is $\delta$-typical when $|\#a-n\lambda_a|<n\delta$ for every supported eigenvector. Let $T_{n,\delta}$ be the span of these product eigenvectors and let $\pi_{n,\delta}$ be its projector divided by its dimension. There is a sequence $\delta_n\to0$, positive with $\dim T_{n,\delta_n}>0$ for every $n\ge1$, such that simultaneously
--
--   $$\frac{\log_2\dim T_{n,\delta_n}}n\longrightarrow H(\rho),\qquad \frac{H(\mathcal N^{\otimes n}(\pi_{n,\delta_n}))}n\longrightarrow H(\mathcal N(\rho)),\qquad \frac{H(\mathcal F^{\otimes n}(\pi_{n,\delta_n}))}n\longrightarrow H(\mathcal F(\rho)).$$
--
--   Entropies are in bits. The second map need not be complementary to the first. The logarithm in the dimension term corrects the printed omission in Eq.(19), consistently with pp.12 and 15; this correction requires independent moderation.
-- source:
--   Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem, arXiv:quant-ph/0106052v2, PDF p. 13, Lemma 1, both statements: simultaneous frequency-typical output entropy limits

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

noncomputable section

open scoped ComplexConjugate Matrix

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

/-- PDF pp.12--13,15, Lemma 1: a single sequence for both CPTP maps.
Printed Eq.(19) omits log. Use log2(dim T_n)/n, required by pp.12,15.
This disclosed source correction awaits independent moderation. -/
theorem simultaneousTypicalEntropyLimits {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    [Nonempty A] [Nonempty B] [Nonempty E]
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho)
    (U : Matrix.unitaryGroup A ℂ) (lam : A → ℝ) (hspec : IsSpectralData rho U lam)
    (N : Superop A B) (hN : IsChannel N) (F : Superop A E) (hF : IsChannel F) :
    ∃ delta : ℕ → ℝ,
      (∀ n, 0 < n → 0 < delta n ∧ 0 < (typicalWords lam n (delta n)).card) ∧
      Tendsto delta atTop (nhds 0) ∧
      Tendsto (fun n => Real.logb 2 ((typicalWords lam n (delta n)).card : ℝ) / n)
        atTop (nhds (vnEntropy rho)) ∧
      Tendsto (fun n => vnEntropy (piSuperop (fun _ : Fin n => N)
        (typicalState U lam n (delta n))) / n) atTop (nhds (vnEntropy (N rho))) ∧
      Tendsto (fun n => vnEntropy (piSuperop (fun _ : Fin n => F)
        (typicalState U lam n (delta n))) / n) atTop (nhds (vnEntropy (F rho))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P45

end
