-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_hamiltonianGibbs_eq_spectralGibbsDensity
-- name    : QEC.Semantics.Davies.hamiltonianGibbs_eq_spectralGibbsDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:01.316185+00:00
-- url     : https://prove2.me/theorems/2b627451-323e-4f96-9714-ba5b4907d950
-- title:
--   Davies: hamiltonian Gibbs eq spectral Gibbs Density
-- statement:
--   Compatibility with any genuine eigenbasis, including the M11 factorization
--   basis; no equality of Gibbs states is an input hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L76-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L76-L84

import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

theorem QEC.Semantics.Davies.hamiltonianGibbs_eq_spectralGibbsDensity {ι : Type} [Fintype ι] [Nonempty ι]
    (H : Operator V) (hH : H.IsSymmetric) (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (heigen : ∀ i, H (b i) = (e i : ℂ) • b i) (β : ℝ) :
    (hamiltonianGibbs H hH β).toOperator = (spectralGibbsDensity b e β).toOperator := by sorry
