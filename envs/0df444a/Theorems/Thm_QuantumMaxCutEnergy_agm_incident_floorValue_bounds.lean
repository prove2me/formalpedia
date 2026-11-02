-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_incident_floorValue_bounds
-- name    : QuantumMaxCutEnergy.agm_incident_floorValue_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:53:34.30695+00:00
-- url     : https://prove2.me/theorems/0041f5c8-2b4c-4e39-bcc7-54e3a7c76ae6
-- title:
--   Certified bounds for the concrete matching and forest estimator
-- statement:
--   For every campaign input G, the particular executable function QMCNumericRuntime.IncidentRuntime.floorValue is a sound numerical lower estimate of OPT. There are weights 0≤m≤f≤W satisfying OPT≤W+(m+f)/2, and this same function dominates f and (W+3m)/2. The concrete function and its exact finite Boolean-machine runtime are defined in QuantumMaxCutFiniteNumericRuntime. This pointwise theorem lets later proofs compose the same implemented function, rather than merely an unspecified existential estimator.
-- source:
--   Numerical-estimation implementation of Anshu, Gosset and Morenz, TQC 2020, Lemmas 5 and 7 and Eqs. (25)–(26). https://doi.org/10.4230/LIPIcs.TQC.2020.7 . Concrete per-instance bounds; not a verbatim standalone theorem statement in the paper.

import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators

theorem QuantumMaxCutEnergy.agm_incident_floorValue_bounds
    (G : QuantumMaxCutEnergy.Input) :
    (QMCNumericRuntime.IncidentRuntime.floorValue G : ℝ) ≤ QuantumMaxCutEnergy.optimum G ∧
    ∃ m f : ℝ,
      0 ≤ m ∧ m ≤ f ∧ f ≤ (∑ e, (G.weights e : ℝ)) ∧
      QuantumMaxCutEnergy.optimum G ≤ (∑ e, (G.weights e : ℝ)) + (m + f) / 2 ∧
      f ≤ (QMCNumericRuntime.IncidentRuntime.floorValue G : ℝ) ∧
      ((∑ e, (G.weights e : ℝ)) + 3 * m) / 2 ≤
        (QMCNumericRuntime.IncidentRuntime.floorValue G : ℝ) := by sorry
