-- Prove2me | Theorems.Thm_QEC_Bounds_linearMap_intertwining_four_stage
-- name    : QEC.Bounds.linearMap_intertwining_four_stage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-18T07:03:22.32414+00:00
-- url     : https://prove2.me/theorems/8fb4c59a-739b-46ce-9859-860f6b6fbe9a
-- title:
--   Bounds: linear Map intertwining four stage
-- statement:
--   The Bounds construction uses the linear Map intertwining four stage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/IntertwiningAlgebra.lean#L14-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/IntertwiningAlgebra.lean#L14-L47

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_JointCoordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_IntertwiningAlgebra
set_option autoImplicit false
open QEC
open QEC.Bounds
universe u

theorem QEC.Bounds.linearMap_intertwining_four_stage
    {H0 H1 H2 H3 H4 : Type u}
    [AddCommMonoid H0] [Module Complex H0]
    [AddCommMonoid H1] [Module Complex H1]
    [AddCommMonoid H2] [Module Complex H2]
    [AddCommMonoid H3] [Module Complex H3]
    [AddCommMonoid H4] [Module Complex H4]
    (J : H1 →ₗ[Complex] H0) (T : H2 →ₗ[Complex] H1)
    (C : H3 →ₗ[Complex] H2) (O : H4 →ₗ[Complex] H3)
    (V0 : H0 →ₗ[Complex] H0) (V1 : H1 →ₗ[Complex] H1)
    (V2 : H2 →ₗ[Complex] H2) (V3 : H3 →ₗ[Complex] H3)
    (V4 : H4 →ₗ[Complex] H4)
    (h0 : V0.comp J = J.comp V1)
    (h1 : V1.comp T = T.comp V2)
    (h2 : V2.comp C = C.comp V3)
    (h3 : V3.comp O = O.comp V4) :
    V0.comp (J.comp (T.comp (C.comp O))) =
      (J.comp (T.comp (C.comp O))).comp V4 := by sorry
