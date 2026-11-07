-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_two_mul_four_r_mul_medium_card_le_nonheavy_weight
-- name    : QEC.Coding.FiberBundle.TwistGraph.two_mul_four_r_mul_medium_card_le_nonheavy_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:36.505386+00:00
-- url     : https://prove2.me/theorems/9ef2a2fc-b600-4256-930f-ae55394d0e1c
-- title:
--   Twist Graph: two mul four r mul medium card le nonheavy weight
-- statement:
--   Medium layers contribute at least `2n / Delta` each.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L944-L976
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L944-L976

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.two_mul_four_r_mul_medium_card_le_nonheavy_weight
    {r ell : Nat}
    [NeZero r] [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    2 * (4 * r) * (mediumLayerSet Delta w).card ≤
      Delta *
        (∑ u ∈ nonheavyLayerSet Delta w,
          HammingWeight (layerWord w u)) := by sorry
