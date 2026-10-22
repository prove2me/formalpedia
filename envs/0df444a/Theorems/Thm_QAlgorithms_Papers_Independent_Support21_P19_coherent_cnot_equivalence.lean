-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_coherent_cnot_equivalence
-- name    : QAlgorithms.Papers.Independent.Support21.P19.coherent_cnot_equivalence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T05:02:05.745303+00:00
-- url     : https://prove2.me/theorems/0dc53949-366b-4eb5-bd40-e993ff7af94b
-- title:
--   Coherent simulation and catalytic CNOT equivalence
-- statement:
--   Free local operations together with one coherent bit in each direction and one EPR pair simulate an unknown-input distributed CNOT and return two decoupled EPR pairs:
--
--   $$
--   [q\to qq]+[qq\leftarrow q]+[qq]\ge\mathrm{CNOT}+2[qq].
--   $$
--
--   Moreover, there is a finite integer $k\ge0$ for which both exact catalytic conversions hold:
--
--   $$
--   [q\to qq]+[qq\leftarrow q]+k[qq]\ge\mathrm{CNOT}+(k+1)[qq],
--   $$
--   $$
--   \mathrm{CNOT}+(k+1)[qq]\ge[q\to qq]+[qq\leftarrow q]+k[qq].
--   $$
--
--   Every returned EPR factor is decoupled from the task. Exactness holds for all operators and hence arbitrary external references. These conversions give the source's catalytic CNOT equivalence.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 2, Coherent simulation and catalytic CNOT equivalence

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2: finite coherent Gottesman simulation and both catalytic CNOT equivalence directions.
In the reverse direction one EPR pair is consumed and k are returned as the catalyst. -/
theorem coherent_cnot_equivalence :
    Exact (idle 1 1) (budget 0 1 0 0 1 1 0 0) (tensorResources cnotResource (resourceTensorCopies (entangled 2) 2)) ∧
    ∃ k : ℕ,
      Exact (idle 1 1) (budget 0 k 0 0 1 1 0 0) (tensorResources cnotResource (resourceTensorCopies (entangled 2) (k+1))) ∧
      Exact cnotResource (budget 1 (k+1) 0 0 0 0 0 0)
        (tensorResources (tensorResources (cobitChannel 2) (reverse (cobitChannel 2))) (resourceTensorCopies (entangled 2) k)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
