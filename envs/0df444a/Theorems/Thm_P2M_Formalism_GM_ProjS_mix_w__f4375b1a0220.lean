-- Prove2me | Theorems.Thm_P2M_Formalism_GM_ProjS_mix_w__f4375b1a0220
-- name    : P2M_Formalism_GM_ProjS_mix_w__f4375b1a0220
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:19.436811+00:00
-- url     : https://prove2.me/theorems/58d1b66b-aaff-49ac-9c8e-8584811c4438
-- title:
--   P2 M Formalism GM Proj S mix w  f4375b1a0220: P2 M Formalism GM Proj S mix w  f4375b1a0220
-- statement:
--   The P2 M Formalism GM Proj S mix w  f4375b1a0220 construction uses the P2 M Formalism GM Proj S mix w  f4375b1a0220 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L491-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L491-L499

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}

theorem P2M_Formalism_GM_ProjS_mix_w__f4375b1a0220 (hv : M.TieVars w e zv sv) :
    ∀ c, ((∃ d, (Fin.cons zv w : Fin (r + 1) → σ) d = w c) ∧ ∀ d, (Fin.cons zv w : Fin (r + 1) → σ) d ≠ e c) ∨
      ((∀ d, (Fin.cons zv w : Fin (r + 1) → σ) d ≠ w c) ∧ ∃ d, (Fin.cons zv w : Fin (r + 1) → σ) d = e c) := by sorry

alias «Formalism».«GM».«ProjS».«mix_w'» := P2M_Formalism_GM_ProjS_mix_w__f4375b1a0220
