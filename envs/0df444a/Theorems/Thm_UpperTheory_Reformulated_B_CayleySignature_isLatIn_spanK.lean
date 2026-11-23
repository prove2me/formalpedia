-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_CayleySignature_isLatIn_spanK
-- name    : UpperTheory.Reformulated.B.CayleySignature.isLatIn_spanK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:47.090481+00:00
-- url     : https://prove2.me/theorems/7b1cbb9a-fdaf-4170-a09c-cc577c6f63f6
-- title:
--   Cayley Signature: is Lat In span K
-- statement:
--   The Cayley Signature construction uses the is Lat In span K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CayleySignature.lean#L9-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CayleySignature.lean#L9-L36

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleySignature
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.CayleySignature.isLatIn_spanK :
    ∀ {O K V : Type} [inst : CommRing O] [IsDomain O] [inst_2 : Field K] [inst_3 : Algebra O K] [IsFractionRing O K]
      [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V] [inst_7 : _root_.Module O V] [inst_8 : IsScalarTower O K V]
      {N : Submodule O V}, N.FG → UpperTheory.Reformulated.B.CayleySignature.IsLatIn N (Submodule.restrictScalars O (Submodule.span K (↑N : Set V))) := by sorry
