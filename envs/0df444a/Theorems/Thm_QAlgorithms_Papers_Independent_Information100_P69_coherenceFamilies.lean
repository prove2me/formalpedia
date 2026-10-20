-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_coherenceFamilies
-- name    : QAlgorithms.Papers.Independent.Information100.P69.coherenceFamilies
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:04:46.610053+00:00
-- url     : https://prove2.me/theorems/b90c2174-ac00-4eb2-bc17-84334db2bd1e
-- title:
--   Coherence-restricted channels
-- statement:
--   Fix the product reference bases, let $\Delta_A,\Delta_B$ be dephasing, and use maximally mixed witnesses $\tau=I_A/a$, $\omega=I_B/b$. The full block MIO and DIO families are, respectively,
--   $$\Delta_B^{\otimes n}M\Delta_A^{\otimes n}=M\Delta_A^{\otimes n},\qquad\Delta_B^{\otimes n}M=M\Delta_A^{\otimes n}.$$
--   Both satisfy F1–F5. For every target channel, the full Stein identity of Theorem 2, smoothed AEP of Theorem 11, and operational threshold of Theorem 12 hold for each family. This applies to the full correlated block-channel classes, with MIO and DIO kept distinct.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 22, Proposition 20

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Proposition 20, full MIO and DIO block classes, PDF p.22.
The instantiated asymptotic conclusions are included for every target. -/
theorem coherenceFamilies [Nonempty A] [Nonempty B] :
    ∀ F ∈ ({mioFamily, dioFamily} : Set (BlockFamily A B)),
      Admissible F mixed ∧ Additional F mixed ∧
      ∀ N : Superop A B, IsChannel N → SteinConclusion N F mixed ∧ OperationalConclusion N F ∧
        (∀ delta : ℕ → ℝ, ∀ bar : ℝ, bar < 2 →
          (∀ n, 1 ≤ n → 0 < delta n ∧ delta n ≤ bar) →
          Tendsto (fun j : ℕ => Real.logb 2 (1/delta (j+1))/(j+1)) atTop (nhds 0) →
          Tendsto (fun j : ℕ => smoothCost (power N (j+1)) (F (j+1)) (delta (j+1))/(j+1))
            atTop (nhds (ENNReal.ofReal (rate N F)))) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
