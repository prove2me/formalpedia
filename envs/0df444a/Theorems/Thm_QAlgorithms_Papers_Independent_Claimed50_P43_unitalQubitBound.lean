-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_unitalQubitBound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.unitalQubitBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:24:59.22048+00:00
-- url     : https://prove2.me/theorems/3bebb02a-4dc6-45f0-9aa0-3f60a3963b64
-- title:
--   Full assisted capacity versus one-shot Holevo capacity for unital qubit channels
-- statement:
--   Let $\Phi$ be a CPTP map on a two-dimensional Hilbert space and suppose it is unital: $\Phi(I)=I$. With capacities in bits,
--
--   $$C_{\rm ea}(\Phi)\le C^{(1)}(\Phi)+1.$$
--
--   The left side is full regularized assisted capacity and the right side uses the one-shot unassisted Holevo capacity. This is the special class for which the paper asserts its stronger comparison.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 7, §III, unnumbered special-case one-shot bound: unital qubit channels

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.7: the conjectured one-shot-right-hand-side bound is asserted for unital
qubit channels. The left side is full assisted capacity. -/
theorem unitalQubitBound (N : Superop (Fin 2) (Fin 2)) (hN : IsChannel N)
    (hunital : N 1 = 1) :
    regularizedAssistedHolevo N ≤ holevoCapacity N + 1 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
