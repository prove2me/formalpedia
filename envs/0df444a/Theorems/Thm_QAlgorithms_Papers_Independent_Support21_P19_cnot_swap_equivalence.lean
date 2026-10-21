-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_cnot_swap_equivalence
-- name    : QAlgorithms.Papers.Independent.Support21.P19.cnot_swap_equivalence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T05:04:28.194979+00:00
-- url     : https://prove2.me/theorems/a926c977-72de-46ed-a994-f2e4f11de296
-- title:
--   Catalytic equivalence of two CNOTs and SWAP
-- statement:
--   There is an integer $k\ge0$ for which two CNOT resource calls and one SWAP resource call simulate each other exactly with an EPR catalyst:
--
--   $$
--   2\,\mathrm{CNOT}+k[qq]\ge\mathrm{SWAP}+k[qq],\qquad
--   \mathrm{SWAP}+k[qq]\ge2\,\mathrm{CNOT}+k[qq].
--   $$
--
--   The two target CNOTs act on independently supplied unknown inputs. Protocols may interleave resource calls with free local operations and reuse returned workspace; the catalyst is returned decoupled from all task outputs. This is a resource equivalence, rather than a two-gate bare circuit identity for SWAP.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 3, Catalytic equivalence of two CNOTs and SWAP

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3: two CNOTs equal SWAP with returned, decoupled EPR catalysis.
This is not a bare two-CNOT synthesis identity. -/
theorem cnot_swap_equivalence :
    ∃ k : ℕ,
      Exact cnotResource (budget 2 k 0 0 0 0 0 0) (tensorResources swapResource (resourceTensorCopies (entangled 2) k)) ∧
      Exact swapResource (budget 1 k 0 0 0 0 0 0) (tensorResources (resourceTensorCopies cnotResource 2) (resourceTensorCopies (entangled 2) k)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
