-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BModbound_relIndex_eq
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BModbound.relIndex_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:57.626705+00:00
-- url     : https://prove2.me/theorems/a539e6ac-cae4-4299-bfe9-71433cc19dea
-- title:
--   BModbound: rel Index eq
-- statement:
--   The BModbound construction uses the rel Index eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/RelIndexEq.lean#L5-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/RelIndexEq.lean#L5-L51

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_RelIndexEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound

theorem PositivityTheory.RgUd.T.Nil.Orb.BModbound.relIndex_eq {k : Type} [Field k] {n : ℕ} (I J : AddSubgroup (Matrix (Fin n) (Fin n) k))
    (GI GJ : Subgroup (GL (Fin n) k)) (hJI : J ≤ I)
    (hGI : ∀ u : GL (Fin n) k, u ∈ GI ↔ u.val - 1 ∈ I)
    (hGJ : ∀ u : GL (Fin n) k, u ∈ GJ ↔ u.val - 1 ∈ J)
    (hsurj : ∀ x ∈ I, ∃ u : GL (Fin n) k, u.val = 1 + x)
    (hmul : ∀ u ∈ GI, ∀ y ∈ J, u.val * y ∈ J) :
    GJ.relIndex GI = J.relIndex I := by sorry
