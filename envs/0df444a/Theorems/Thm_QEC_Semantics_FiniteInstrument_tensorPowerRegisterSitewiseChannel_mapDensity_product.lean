-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerRegisterSitewiseChannel_mapDensity_product
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerRegisterSitewiseChannel_mapDensity_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:08:53.429199+00:00
-- url     : https://prove2.me/theorems/c6df445a-ba21-4418-b173-2f1faa489213
-- title:
--   Finite Instrument: tensor Power Register Sitewise Channel map Density product
-- statement:
--   The flattened sitewise channel maps a genuine block-product density to
--   the block-product of the one-block channel outputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/ChannelProduct.lean#L40-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/ChannelProduct.lean#L40-L59

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
import Definitions.Def_QEC_Semantics_Instruments_Registers_ChannelProduct
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteInstrument.tensorPowerRegisterSitewiseChannel_mapDensity_product
    (channel : QuantumChannel (Qubit.QubitRegister ι) (Qubit.QubitRegister ι))
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (Qubit.QubitRegister ι) 0))
    (attempts : Nat) :
    (tensorPowerRegisterSitewiseChannel channel attempts).mapDensity
        (tensorPowerRegisterProductDensity ι rho rhoUnit attempts) =
      tensorPowerRegisterProductDensity ι (channel.mapDensity rho) rhoUnit attempts := by sorry
