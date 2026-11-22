-- Prove2me | Theorems.Thm_P2M_Formalism_CountingSumsFrames_fockN_smul_right__bfa97ee757de
-- name    : P2M_Formalism_CountingSumsFrames_fockN_smul_right__bfa97ee757de
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:43.71893+00:00
-- url     : https://prove2.me/theorems/5ed74c31-58e9-4236-8e0d-917b2f0465ed
-- title:
--   P2 M Formalism Counting Sums Frames fock N smul right  bfa97ee757de: P2 M Formalism Counting Sums Frames fock N smul right  bfa97ee757de
-- statement:
--   The P2 M Formalism Counting Sums Frames fock N smul right  bfa97ee757de construction uses the P2 M Formalism Counting Sums Frames fock N smul right  bfa97ee757de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L274-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L274-L277

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem P2M_Formalism_CountingSumsFrames_fockN_smul_right__bfa97ee757de {N r : ℕ} (LL : Letters N) (c : ℚ_[p]) (F G : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    fockN p LL F (c • G) = c * fockN p LL F G := by sorry

alias «Formalism».«CountingSumsFrames».«fockN_smul_right'» := P2M_Formalism_CountingSumsFrames_fockN_smul_right__bfa97ee757de
