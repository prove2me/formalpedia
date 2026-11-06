-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_bornWeight_fst_filter_sum
-- name    : QEC.Semantics.FiniteInstrument.bind_bornWeight_fst_filter_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:02:51.049194+00:00
-- url     : https://prove2.me/theorems/1880f5d1-570c-47f7-8cde-f18d09058b9f
-- title:
--   Finite Instrument: bind born Weight fst filter sum
-- statement:
--   Filtering a complete fixed-raw-index bind by a predicate on the retained
--   predecessor observation preserves exactly the corresponding filtered Born
--   mass.  The successor outcomes are all summed, so no independence premise is
--   needed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/BornMass.lean#L108-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/BornMass.lean#L108-L125

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_Sequential_BornMass
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Omega -> Type x} [forall outcome, Fintype (kappaTwo outcome)]
variable {Xi : Omega -> Type y} [forall outcome, Fintype (Xi outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
variable {kappaPrime : Type x} [Fintype kappaPrime]

theorem QEC.Semantics.FiniteInstrument.bind_bornWeight_fst_filter_sum
    (I : FiniteInstrument kappa Omega H K)
    (J : (outcome : Omega) -> FiniteInstrument kappaPrime (Xi outcome) K L)
    (hJ : forall outcome, (J outcome).kraus.Complete)
    (predicate : Omega -> Prop) [DecidablePred predicate]
    (rho : DensityOperator H) :
    (∑ outcome ∈ Finset.univ.filter
        (fun outcome : Sigma Xi => predicate outcome.1),
      (I.bind J).bornWeight outcome rho) =
      ∑ outcome ∈ Finset.univ.filter predicate, I.bornWeight outcome rho := by sorry
