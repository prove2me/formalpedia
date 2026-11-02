-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_moment_correlation_range
-- name    : QuantumMaxCutEnergy.PauliSDP.moment_correlation_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T04:15:02.364439+00:00
-- url     : https://prove2.me/theorems/0b114ffd-3561-49c8-8b56-fb3dd4426381
-- title:
--   Per-edge moment range: $-3 \\le L(XX)+L(YY)+L(ZZ) \\le 1$
-- statement:
--   The full per-edge range of the level-2 Pauli-moment relaxation.
--
--   For every feasible level-$k$ ($k \ge 2$) moment solution $L$ and every pair $i \ne j$,
--   $$-3 \;\le\; L(X_iX_j) + L(Y_iY_j) + L(Z_iZ_j) \;\le\; 1.$$
--   The upper bound is the product-state correlation bound (the per-edge expectation $(1 - \Sigma L)/2$ is nonnegative); the lower bound says each edge expectation is at most $2$ (the singlet value). Together they pin the interval in which the level-2 analysis' parameter $s = -(\Sigma L)/3$ lives: $s \in [-1/3, 1]$, and the edge coefficient $c_e = (1+3s)/2 \in [0,2]$. Role: the range inputs of the Lee–Parekh integrality analysis. **Formalization Note.** The upper half is also available separately as `moment_correlation_bound`; this theorem adds the lower half and the joint form.
-- source:
--   Extracted from the level-2 Quantum Max-Cut analysis of Eunou Lee and Ojas Parekh, ICALP 2024, https://arxiv.org/abs/2401.03616

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.PauliSDP.moment_correlation_range {n k : ℕ} (hk : 2 ≤ k)
    (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ) (hL : QuantumMaxCutEnergy.PauliSDP.Feasible k L)
    (i j : Fin n) (hij : i ≠ j) :
    -(3 : ℝ) ≤ L (fun t => if t = i ∨ t = j then 1 else 0) +
        L (fun t => if t = i ∨ t = j then 2 else 0) +
        L (fun t => if t = i ∨ t = j then 3 else 0) ∧
      L (fun t => if t = i ∨ t = j then 1 else 0) +
        L (fun t => if t = i ∨ t = j then 2 else 0) +
        L (fun t => if t = i ∨ t = j then 3 else 0) ≤ 1 := by sorry
