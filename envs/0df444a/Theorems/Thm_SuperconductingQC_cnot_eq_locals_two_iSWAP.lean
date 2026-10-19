-- Prove2me | Theorems.Thm_SuperconductingQC_cnot_eq_locals_two_iSWAP
-- name    : SuperconductingQC.cnot_eq_locals_two_iSWAP
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T01:25:51.562879+00:00
-- url     : https://prove2.me/theorems/8e5eb18e-2707-48b3-afd9-a46aa65adfbe
-- title:
--   CNOT from two iSWAP gates and single-qubit gates
-- statement:
--   There exist single-qubit unitaries $A,B,C,D,E,F\in U(2)$ such that
--   $$\mathrm{CNOT}=(A\otimes B)\,\mathrm{iSWAP}\,(C\otimes D)\,\mathrm{iSWAP}\,(E\otimes F),$$
--   where CNOT has the first qubit as control.
--
--   The equality is exact (no global phase is discarded; a phase can be absorbed into $A$). This is the bridge from the CNOT-based universality theorem to the iSWAP gate natively available on coupled transmons.
-- source:
--   N. Schuch, J. Siewert, Natural two-qubit gate for quantum computation using the XY interaction, Phys. Rev. A 67, 032301 (2003), https://doi.org/10.1103/PhysRevA.67.032301 (CNOT from two iSWAP gates)

import Mathlib
import Definitions.Def_SuperconductingQC_Gates

open scoped Matrix Kronecker

namespace SuperconductingQC

theorem cnot_eq_locals_two_iSWAP :
    ∃ A B C D E F : Matrix (Fin 2) (Fin 2) ℂ,
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ B ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      C ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ D ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      E ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ F ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      CNOT = (A ⊗ₖ B) * iSWAP * (C ⊗ₖ D) * iSWAP * (E ⊗ₖ F) := by
  sorry

end SuperconductingQC
