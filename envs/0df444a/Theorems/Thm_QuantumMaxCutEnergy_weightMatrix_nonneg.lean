-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_weightMatrix_nonneg
-- name    : QuantumMaxCutEnergy.weightMatrix_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:16:53.384204+00:00
-- url     : https://prove2.me/theorems/44f714d4-184a-47c6-9ceb-311063c0f55d
-- title:
--   The weight matrix of a Quantum Max Cut input has nonnegative entries
-- statement:
--   Every entry of the symmetric weight matrix $A(G)$ of a Quantum Max Cut input is nonnegative: off the diagonal it is a weight, which lies in $\mathbb Q_{\ge0}$, and it vanishes on the diagonal.
--
--   This is what allows a *per-pair* bound to be summed against the weights: the inequality $1-\mathbb E\langle r_i,r_j\rangle \ge 0.954(1-X_{ij})$ can be multiplied by $A_{ij}\ge0$ and summed without introducing a sign problem.
-- source:
--   QuantumMaxCutEnergy.weightMatrix: weights are ℚ≥0 by definition of Input.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open MeasureTheory Matrix
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- The weight matrix has nonnegative entries. -/
theorem weightMatrix_nonneg (G : Input) (i j : Fin G.n) : 0 ≤ weightMatrix G i j := by sorry

end QuantumMaxCutEnergy
