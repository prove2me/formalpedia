-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_initial_dimension_square_bounds
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.initial_dimension_square_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:42:58.8982+00:00
-- url     : https://prove2.me/theorems/b368648b-8313-43f0-8648-f24a967b1028
-- title:
--   HHO20 Distance Balancing: initial dimension square bounds
-- statement:
--   Exact finite form of the unreduced `K = Theta(sqrt N)` claim.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L421-L428
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L421-L428

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.initial_dimension_square_bounds (s : Nat) (hs : 200 ≤ s) :
    initialBlocklengthAt s ≤ 7 * initialDimensionAt s ^ 2 ∧
    7 * initialDimensionAt s ^ 2 ≤ 2 * initialBlocklengthAt s := by sorry
