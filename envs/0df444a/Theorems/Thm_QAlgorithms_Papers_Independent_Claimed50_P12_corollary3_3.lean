-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_corollary3_3
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.corollary3_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:35:24.442983+00:00
-- url     : https://prove2.me/theorems/961f525b-ddb5-4c42-b0e2-7c93bb57d0bb
-- title:
--   Universal law on channels in complete-positive order
-- statement:
--   Let $D,E$ be nonzero finite-dimensional complex Hilbert spaces and set $d=(\dim D)(\dim E)^2$. There is a probability law $\mu$ on CPTP maps $\tau:D\to E$, chosen before the copy count and target channel. Every permutation-covariant CPTP map $W:D^{\otimes n}\to E^{\otimes n}$, for $n\ge1$, satisfies
--
--   $$ (n+1)^{d^2-1}\int\tau^{\otimes n}\,d\mu(\tau)-W\quad\text{is completely positive}.$$
--
--   Covariance intertwines the input and output permutation actions. The integral is coefficientwise and integrable on every input operator, including entangled inputs. This is the channel version of the extension reduction.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 12, Corollary 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Corollary 3.3 (PDF p.12 fn.5): the difference is COMPLETELY positive.
The probability law precedes the copy count and the covariant channel. -/
theorem corollary3_3 {D E : Type*} [Fintype D] [Fintype E]
    [DecidableEq D] [DecidableEq E] [Nonempty D] [Nonempty E] :
    letI := channelMeasurable D E
    ∃ mu : Measure {W : Superop D E // IsChannel W}, IsProbabilityMeasure mu ∧
      (∀ (n : ℕ) (X : Op (Fin n → D)) y z,
        Integrable (fun W => piSuperop (fun _ : Fin n => W.val) X y z) mu) ∧
      ∀ (n : ℕ), 0 < n → ∀ W : Superop (Fin n → D) (Fin n → E),
        IsChannel W → copyPermutationCovariant W →
        CP (fun X => (((((n+1 : ℕ) : ℝ) ^ (dimensionParameter D E ^ 2 - 1) : ℝ) : ℂ) •
          meanChannel mu n X - W X)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
