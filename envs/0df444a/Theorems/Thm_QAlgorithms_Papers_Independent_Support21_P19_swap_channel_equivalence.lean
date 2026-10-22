-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_swap_channel_equivalence
-- name    : QAlgorithms.Papers.Independent.Support21.P19.swap_channel_equivalence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T05:03:30.230986+00:00
-- url     : https://prove2.me/theorems/303872a5-0b4e-46a3-b589-daf5b4775e0a
-- title:
--   SWAP and two oppositely directed qubit channels
-- statement:
--   SWAP on two unknown qubits is catalytically equivalent to one quantum channel in each direction. Specifically, there is an integer $k\ge0$ such that
--
--   $$
--   \mathrm{SWAP}+k[qq]\ge[q\to q]+[q\leftarrow q]+k[qq],
--   $$
--   $$
--   [q\to q]+[q\leftarrow q]+k[qq]\ge\mathrm{SWAP}+k[qq].
--   $$
--
--   Both simulations are exact bipartite channel simulations with free local operations, counted nonlocal calls, and a returned decoupled EPR catalyst. Unknown inputs may be entangled with each other and with external references.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 2, SWAP and two oppositely directed qubit channels

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2: catalytic SWAP versus two opposite quantum channels, on arbitrary quantum inputs. -/
theorem swap_channel_equivalence :
    ∃ k : ℕ,
      Exact swapResource (budget 1 k 0 0 0 0 0 0)
        (tensorResources (tensorResources (qubitChannel 2) (reverse (qubitChannel 2))) (resourceTensorCopies (entangled 2) k)) ∧
      Exact (idle 1 1) (budget 0 k 1 1 0 0 0 0) (tensorResources swapResource (resourceTensorCopies (entangled 2) k)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
