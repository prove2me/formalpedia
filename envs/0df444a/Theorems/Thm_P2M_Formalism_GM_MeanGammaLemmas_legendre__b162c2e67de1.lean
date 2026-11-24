-- Prove2me | Theorems.Thm_P2M_Formalism_GM_MeanGammaLemmas_legendre__b162c2e67de1
-- name    : P2M_Formalism_GM_MeanGammaLemmas_legendre__b162c2e67de1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:09.360514+00:00
-- url     : https://prove2.me/theorems/6bd5e6c1-6308-4b21-b780-20f8589a3e82
-- title:
--   P2 M Formalism GM Mean Gamma Lemmas legendre  b162c2e67de1: P2 M Formalism GM Mean Gamma Lemmas legendre  b162c2e67de1
-- statement:
--   The P2 M Formalism GM Mean Gamma Lemmas legendre  b162c2e67de1 construction uses the P2 M Formalism GM Mean Gamma Lemmas legendre  b162c2e67de1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L208-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L208-L235

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Finset

theorem P2M_Formalism_GM_MeanGammaLemmas_legendre__b162c2e67de1 (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (n : ℝ) / ((p : ℝ) - 1) - (padicValNat p n.factorial : ℝ) ≤ (Nat.log p n : ℝ) + 1 := by sorry

alias «Formalism».«GM».«MeanGammaLemmas».«legendre'» := P2M_Formalism_GM_MeanGammaLemmas_legendre__b162c2e67de1
