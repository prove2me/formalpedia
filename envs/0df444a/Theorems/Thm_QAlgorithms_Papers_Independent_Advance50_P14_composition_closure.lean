-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_composition_closure
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.composition_closure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:21:09.94728+00:00
-- url     : https://prove2.me/theorems/09ffc26d-6e1c-4acd-9c51-9b409b227a62
-- title:
--   Section VI unnumbered: quantitative composition closure
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. An operation is CPTP; its separability constraint applies only to the specified input and output partitions. Let $\Omega:A\to B$ be $\delta$-non-entangling and $\Lambda:B\to C$ be $\epsilon$-non-entangling, where the intermediate system and its partition agree and $\epsilon,\delta\ge0$. Then
--
--   $$\Lambda\circ\Omega\in{\rm SEPP}(\epsilon+\delta+\delta\epsilon).$$
--
--   For sequences of such operations, with arbitrary compatible finite block spaces, both leakages tending to zero imply that the displayed composite leakage also tends to zero. This is composition closure; it imposes no tensor or ancillary closure.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 18, Section VI unnumbered: quantitative composition closure

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF p.18: quantitative composition closure with matching intermediate
partition, and the corresponding vanishing-leakage sequence closure. -/
theorem composition_closure :
    (∀ {m l j : ℕ} (A : MultipartiteRegister m) (B : MultipartiteRegister l) (C : MultipartiteRegister j)
      (epsilon delta : ℝ) (L : Superop (RegisterBasis B.Local) (RegisterBasis C.Local))
      (O : Superop (RegisterBasis A.Local) (RegisterBasis B.Local)),
      EpsilonNonEntangling B C epsilon L → EpsilonNonEntangling A B delta O →
      EpsilonNonEntangling A C (epsilon + delta + delta * epsilon) (L ∘ O)) ∧
    (∀ {m l j : ℕ} (A : ℕ → MultipartiteRegister m) (B : ℕ → MultipartiteRegister l)
      (C : ℕ → MultipartiteRegister j) (epsilon delta : ℕ → ℝ)
      (L : (n : ℕ) → Superop (RegisterBasis (B n).Local) (RegisterBasis (C n).Local))
      (O : (n : ℕ) → Superop (RegisterBasis (A n).Local) (RegisterBasis (B n).Local)),
      (∀ n, EpsilonNonEntangling (B n) (C n) (epsilon n) (L n)) →
      (∀ n, EpsilonNonEntangling (A n) (B n) (delta n) (O n)) →
      Tendsto epsilon atTop (nhds 0) → Tendsto delta atTop (nhds 0) →
      (∀ n, EpsilonNonEntangling (A n) (C n)
        (epsilon n + delta n + delta n * epsilon n) (L n ∘ O n)) ∧
      Tendsto (fun n => epsilon n + delta n + delta n * epsilon n) atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
