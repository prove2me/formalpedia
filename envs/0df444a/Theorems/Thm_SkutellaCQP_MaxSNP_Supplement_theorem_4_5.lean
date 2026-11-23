-- Prove2me | Theorems.Thm_SkutellaCQP_MaxSNP_Supplement_theorem_4_5
-- name    : SkutellaCQP.MaxSNP.Supplement.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:50:08.669323+00:00
-- url     : https://prove2.me/theorems/2237fae3-4028-4828-88d7-db98516aa9e1
-- title:
--   Theorem 4.5 — polynomial-time deterministic factors 3 and 2 against preemptive optima
-- statement:
--   Consider unrelated machines with positive processing times, nonnegative release dates and nonnegative weights. For a suitable polynomial accuracy, the following procedure can be implemented in deterministic polynomial time, and every algorithm that follows it (whatever near-optimal solution it finds and however it breaks ties) is an approximation algorithm with the factors below: compute a sufficiently accurate feasible CQP′ₚ solution, derandomize its slot rounding by conditional expectations, and return the encoded feasible nonpreemptive schedule $S(I)$. For every feasible real-time preemptive schedule $P$,
--   $$\operatorname{VAL}(S(I))\le3\operatorname{VAL}(P),$$
--   and if all release dates vanish,
--   $$\operatorname{VAL}(S(I))\le2\operatorname{VAL}(P).$$
--   The output never migrates, so arbitrary communication delays impose no further restriction on it. Comparing with all preemptive schedules without delays also bounds the optimum with any imposed delays.
--
--   The accuracy polynomial and the machine are conclusions. Integer inputs and arbitrary finitely encoded rational inputs are included. Comparator times are real and may be nonintegral. The result does not infer integrality of the preemptive optimum from integer input.
--
--   Differences from the source:
--   - encoding: polynomial-time near-optimization and DERANDOMIZED ROUNDING → uniform finite-alphabet Turing machines on binary rational data, existential polynomial precision, and encoded output starts; reason: this gives computational meaning to the stated algorithm without assuming a solver oracle
--   - reading: conditional probabilities are not specified further → conditional expectations of the quadratic pessimistic estimator from the slot-start bound on p. 20; reason: its conditional averages are computable without exact expectations of a maximum
--   - encoding: preemptive optimum and arbitrary communication delays → comparison against every bounded measurable real-time preemptive schedule without delays, with a nonpreemptive output; reason: the comparison includes delay-constrained schedules and the output creates no migration delay
--   - encoding: the preemptive relaxation display omits release eligibility (18) → the immutable published CQP′ₚ definition includes (18); reason: the same inherited correction was already moderated; no base item is changed
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), DOI 10.1145/375827.375840, p. 23, Theorem 4.5

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Supplement_PreemptAlgorithm

namespace SkutellaCQP.MaxSNP.Supplement

/-- Theorem 4.5, p. 23: for a suitable accuracy polynomial, the CQP/conditional-expectation
pipeline is implementable in uniform polynomial time, and *every* algorithm following the
pipeline achieves both exact factors against arbitrary real measurable preemptive comparators. -/
theorem theorem_4_5 :
    ∃ q : Polynomial ℕ,
      (∃ A : ReleaseInput → DeroundOutput,
        PolyMap ReleaseInput.code DeroundOutput.code A ∧ PreemptPipeline q A) ∧
      ∀ A : ReleaseInput → DeroundOutput, PreemptPipeline q A →
      ∀ I : ReleaseInput,
        let τ := (A I).slots I
        let S := SkutellaCQP.Preempt.toPSched I.pr I.wr I.rr τ
        SkutellaCQP.Preempt.PFeasible I.pr I.rr S ∧
        SkutellaCQP.Preempt.Nonpreemptive S ∧
        (∀ P : MeasurablePreemptive I.pr I.rr,
          SkutellaCQP.Preempt.pval I.wr S ≤ 3 * P.value I.wr) ∧
        ((∀ i j, I.r i j = 0) → ∀ P : MeasurablePreemptive I.pr I.rr,
          SkutellaCQP.Preempt.pval I.wr S ≤ 2 * P.value I.wr) := by sorry

end SkutellaCQP.MaxSNP.Supplement
