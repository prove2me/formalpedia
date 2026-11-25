-- Prove2me | Theorems.Thm_P2M_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_isChain_apply__4e7af1fbc80f
-- name    : P2M_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_isChain_apply__4e7af1fbc80f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:06:42.390123+00:00
-- url     : https://prove2.me/theorems/2c3c75f3-8286-4f76-ba56-d776989daa40
-- title:
--   P2 M Positivity Theory Rg Ud T Nil Orb BReps cb is Chain apply  4e7af1fbc80f: P2 M Positivity Theory Rg Ud T Nil Orb BReps cb is Chain apply  4e7af1fbc80f
-- statement:
--   The P2 M Positivity Theory Rg Ud T Nil Orb BReps cb is Chain apply  4e7af1fbc80f construction uses the P2 M Positivity Theory Rg Ud T Nil Orb BReps cb is Chain apply  4e7af1fbc80f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/CbIsChainApply.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/CbIsChainApply.lean#L47-L51

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbIsChainApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
open Module Submodule
variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem P2M_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_isChain_apply__4e7af1fbc80f (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) (i : Fin (l a)) :
    B ⟨a, i⟩ = (N ^ (i : ℕ)) (B ⟨a, ⟨0, h0⟩⟩) := by sorry

alias «PositivityTheory».«RgUd».«T».«Nil».«Orb».«BReps».«cb_isChain_apply'» := P2M_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_isChain_apply__4e7af1fbc80f
