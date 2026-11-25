-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBK_mem_rootSet__178724779aab
-- name    : P2M_Formalism_FourierDecayAlt_P_PBK_mem_rootSet__178724779aab
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:53:13.966022+00:00
-- url     : https://prove2.me/theorems/a7c1b695-7926-55bc-8f72-b883d4454b5b
-- title:
--   P2 M Formalism Fourier Decay Alt P PBK mem root Set  178724779aab: P2 M Formalism Fourier Decay Alt P PBK mem root Set  178724779aab
-- statement:
--   The P2 M Formalism Fourier Decay Alt P PBK mem root Set  178724779aab construction uses the P2 M Formalism Fourier Decay Alt P PBK mem root Set  178724779aab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L12-L13

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical

theorem P2M_Formalism_FourierDecayAlt_P_PBK_mem_rootSet__178724779aab {s : ℕ} (hs : s ≠ 0) {a z : ℂ} : z ∈ G.rootSet s a ↔ z ^ s = a := by sorry

alias «Formalism».«FourierDecayAlt».«P».«PBK».«mem_rootSet'» := P2M_Formalism_FourierDecayAlt_P_PBK_mem_rootSet__178724779aab
