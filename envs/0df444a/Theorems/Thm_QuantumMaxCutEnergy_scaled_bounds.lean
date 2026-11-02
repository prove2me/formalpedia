-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_scaled_bounds
-- name    : QuantumMaxCutEnergy.scaled_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:37:18.602169+00:00
-- url     : https://prove2.me/theorems/6e1913a5-2465-43d5-a662-94803d8c8770
-- title:
--   Sound numerical energy estimates from a relaxation integrality gap
-- statement:
--   Let G be an arbitrary nonnegative rational weighted graph with total weight W and quantum optimum O. Suppose a real relaxation value U satisfies O≤U and γU≤O, where γ and the approximation L are nonnegative rationals. If L≤U, U−εW≤L, ε≥0 and α≤γ(1−2ε), then the rational output γL is at most O and at least αO. The result uses the proved inequality W≤2O and includes W=0. It assumes explicit gap and value-precision bounds; it does not assume or prove an SDP algorithm.
-- source:
--   Elementary numerical relaxation-value conversion for the QuantumMaxCutEnergy model, using the verified total-weight lower bound. Application: Lee and Parekh, ICALP2024, Theorem11, https://doi.org/10.4230/LIPIcs.ICALP.2024.105 . This supporting error-conversion lemma is a derived implementation tool, not a verbatim numbered statement in that paper.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.scaled_bounds
    (G : QuantumMaxCutEnergy.Input) (U : ℝ) (L γ : ℚ≥0) (α ε : ℝ)
    (hε : 0 ≤ ε)
    (hupper : QuantumMaxCutEnergy.optimum G ≤ U)
    (hgap : (γ : ℝ) * U ≤ QuantumMaxCutEnergy.optimum G)
    (hbelow : (L : ℝ) ≤ U)
    (hprecision : U - ε * (∑ e, (G.weights e : ℝ)) ≤ (L : ℝ))
    (hmargin : α ≤ (γ : ℝ) * (1 - 2 * ε)) :
    ((γ * L : ℚ≥0) : ℝ) ≤ QuantumMaxCutEnergy.optimum G ∧
      α * QuantumMaxCutEnergy.optimum G ≤ ((γ * L : ℚ≥0) : ℝ) := by sorry
