-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm2020_incident_matching_forest
-- name    : QuantumMaxCutEnergy.agm2020_incident_matching_forest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T01:04:52.431637+00:00
-- url     : https://prove2.me/theorems/f781cc05-efcc-4bbf-b832-a77e21551438
-- title:
--   Incident maxima decompose into a matching and a forest
-- statement:
--   For a finite graph with nonnegative rational weights, let $D$ be the sum, over vertices, of the largest incident edge weight, taking zero at isolated vertices. There exist edge sets $M\subseteq F\subseteq E$ such that $M$ is a matching, $F$ is a forest, and
--
--   $$D=\sum_{e\in M}w_e+\sum_{e\in F}w_e.$$
--
--   This verifies the finite combinatorial conclusion and construction in the published Lemma 7. Its efficient-computation claim remains a separate obligation.
-- source:
--   Anshu, Gosset, and Morenz, TQC 2020, Lemma 7 and its proof, pp. 7:9–7:10. https://doi.org/10.4230/LIPIcs.TQC.2020.7 . The formalization includes M⊆F from the printed construction, matching, actual Mathlib graph acyclicity, and the exact incident-maximum identity with isolated vertices contributing zero. No polynomial-time certificate is claimed.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.agm2020_incident_matching_forest {n : ℕ} (E : Finset (QuantumMaxCutEnergy.Edge n)) (w : QuantumMaxCutEnergy.Weights n) :
    ∃ M F : Finset (QuantumMaxCutEnergy.Edge n), M ⊆ E ∧ F ⊆ E ∧ M ⊆ F ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint
        ({e.val.1, e.val.2} : Finset (Fin n)) {f.val.1, f.val.2}) ∧
      (⨆ e ∈ F, SimpleGraph.edge e.val.1 e.val.2).IsAcyclic ∧
      (∑ v, (((E.filter (fun e => v = e.val.1 ∨ v = e.val.2)).sup w : ℚ≥0) : ℝ)) =
        (∑ e ∈ M, (w e : ℝ)) + ∑ e ∈ F, (w e : ℝ) := by sorry
