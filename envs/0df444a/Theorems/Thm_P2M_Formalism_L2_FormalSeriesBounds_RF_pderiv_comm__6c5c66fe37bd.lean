-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_RF_pderiv_comm__6c5c66fe37bd
-- name    : P2M_Formalism_L2_FormalSeriesBounds_RF_pderiv_comm__6c5c66fe37bd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:46:43.246449+00:00
-- url     : https://prove2.me/theorems/23847c6e-4695-44a7-9b1d-1b6258fcfc60
-- title:
--   P2 M Formalism L2 Formal Series Bounds RF pderiv comm  6c5c66fe37bd: P2 M Formalism L2 Formal Series Bounds RF pderiv comm  6c5c66fe37bd
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds RF pderiv comm  6c5c66fe37bd construction uses the P2 M Formalism L2 Formal Series Bounds RF pderiv comm  6c5c66fe37bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FinTwoNeOneSub.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FinTwoNeOneSub.lean#L12-L25

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj

theorem P2M_Formalism_L2_FormalSeriesBounds_RF_pderiv_comm__6c5c66fe37bd {σ R : Type} [CommRing R] (i j : σ) (p : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«RF».«pderiv_comm'» := P2M_Formalism_L2_FormalSeriesBounds_RF_pderiv_comm__6c5c66fe37bd
