-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P01_pureIntrinsicSquashed
-- name    : QAlgorithms.Papers.Independent.Frontier30.P01.pureIntrinsicSquashed
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:25:15.652834+00:00
-- url     : https://prove2.me/theorems/e2e287fe-30fb-46df-be53-63e252fc9cff
-- title:
--   Pure-state intrinsic information equals twice marginal squashed entanglement
-- statement:
--   Let $|\psi\rangle_{ABE}$ be a unit vector on three finite Hilbert spaces of positive dimension, and let $\rho_{AB}=\operatorname{Tr}_E|\psi\rangle\langle\psi|$. Entropies are measured in bits. Quantum intrinsic information minimizes $I(A:B\mid E')$ over all finite-output CPTP maps $E\to E'$, and squashed entanglement minimizes half the conditional mutual information over all finite extensions of $\rho_{AB}$. Then
--
--   $$
--   I(A:B\downarrow E)_{|\psi\rangle\langle\psi|}=2E_{\rm sq}(\rho_{AB}).
--   $$
--
--   The identity compares the two entropic bounds on a pure tripartite input. The squashed-entanglement argument is the bipartite marginal, with the cut $A:B$.
-- source:
--   Unifying classical and quantum key distillation, arXiv:quant-ph/0608199v3, PDF p. 8, pure-intrinsic-squashed

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P01

namespace QAlgorithms.Papers.Independent.Frontier30.P01

open scoped Matrix ComplexConjugate

noncomputable section

/-- arXiv:quant-ph/0608199v3, PDF pp.8,10, Eq.(18): intrinsic information
of a pure tripartite state is twice squashed entanglement of its AB marginal. -/
theorem pureIntrinsicSquashed {a b e : ℕ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (psi : EuclideanSpace ℂ ((Fin a × Fin b) × Fin e)) (hpsi : ‖psi‖ = 1) :
    2 * Dependency50.P19.squashed (traceRight (pureDensity psi)) =
      intrinsic (pureDensity psi) := by sorry

end

end QAlgorithms.Papers.Independent.Frontier30.P01
