-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P42_private_cost_lower_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P42.private_cost_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:39:09.997483+00:00
-- url     : https://prove2.me/theorems/f53e61ab-8496-4235-9c98-a600a98d6b41
-- title:
--   Private-dit entanglement cost is at least the key size
-- statement:
--   Let $d,a,b$ be positive integers, let $\rho$ be a positive semidefinite trace-one shield state on $\mathbb C^a\otimes\mathbb C^b$, and let each $U_i$ be a unitary on that joint shield. Write
--
--   $$
--   \gamma^{(d)}=\frac1d\sum_{i,j=0}^{d-1}|ii\rangle\langle jj|\otimes U_i\rho U_j^\dagger,
--   $$
--
--   with the bipartition $AA':BB'$ and local shield dimensions $a,b$. All logarithms and resource rates are in bits.
--
--   Let $E_C$ be operational entanglement cost in singlets per input copy, allowing trace-preserving adaptive LOCC, arbitrary local ancillary systems and vanishing preparation error. Then
--
--   $$
--   E_C(\gamma^{(d)})\ge\log_2d.
--   $$
--
--   The statement includes $d=1$. It uses the accepted operational cost, without assuming the formation lower bound for tensor powers or attainment of an optimal cost.
-- source:
--   Quantum states representing perfectly secure bits are always distillable, arXiv:quant-ph/0602176v2, PDF p. 4, III, Property 1a

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

namespace QAlgorithms.Papers.Independent.Gap48.P42

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Property 1a: operational singlet cost is at least log_2 d.
Uses the accepted Hayden--Horodecki--Terhal cost, not a prescribed scalar or
an assumed formation bound for tensor powers. The case d=1 is included. -/
theorem private_cost_lower_bound {d a b : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho)
    (U : Fin d → Matrix.unitaryGroup (Fin a × Fin b) ℂ) :
    Real.logb 2 d ≤ Dependency50.P42.entanglementCost Dependency50.P42.paperBures
      (bipartitePrivate rho U) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P42
