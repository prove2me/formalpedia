-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_hamiltonian_commutes_gibbs
-- name    : QEC.Semantics.Davies.hamiltonian_commutes_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:28:48.784874+00:00
-- url     : https://prove2.me/theorems/a69de1ab-23bd-4f27-b27f-dedd0c709de4
-- title:
--   Davies: hamiltonian commutes gibbs
-- statement:
--   The Davies construction uses the hamiltonian commutes gibbs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L56-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L56-L60

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem QEC.Semantics.Davies.hamiltonian_commutes_gibbs (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β : ℝ) :
    Commute (diagonal b e) (spectralGibbsDensity b e β).toOperator := by sorry
