-- Prove2me | Theorems.Thm_P2M_Formalism_GM_ProjS_mix_e__3cb99070d549
-- name    : P2M_Formalism_GM_ProjS_mix_e__3cb99070d549
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:28.973651+00:00
-- url     : https://prove2.me/theorems/1be906db-e0a6-4569-9b36-575482fcda59
-- title:
--   P2 M Formalism GM Proj S mix e  3cb99070d549: P2 M Formalism GM Proj S mix e  3cb99070d549
-- statement:
--   The P2 M Formalism GM Proj S mix e  3cb99070d549 construction uses the P2 M Formalism GM Proj S mix e  3cb99070d549 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L501-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L501-L509

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

theorem P2M_Formalism_GM_ProjS_mix_e__3cb99070d549 (hv : M.TieVars w e zv sv) :
    ∀ c, ((∃ d, (Fin.cons sv e : Fin (r + 1) → σ) d = w c) ∧ ∀ d, (Fin.cons sv e : Fin (r + 1) → σ) d ≠ e c) ∨
      ((∀ d, (Fin.cons sv e : Fin (r + 1) → σ) d ≠ w c) ∧ ∃ d, (Fin.cons sv e : Fin (r + 1) → σ) d = e c) := by sorry

alias «Formalism».«GM».«ProjS».«mix_e'» := P2M_Formalism_GM_ProjS_mix_e__3cb99070d549
