-- Prove2me | Theorems.Thm_P2M_Formalism_G0_TopsChoiceProbabilityLemmas_tile_sub__fbbb87d340ca
-- name    : P2M_Formalism_G0_TopsChoiceProbabilityLemmas_tile_sub__fbbb87d340ca
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:32.249528+00:00
-- url     : https://prove2.me/theorems/67719c02-33b7-4297-924f-e091918ada10
-- title:
--   P2 M Formalism G0 Tops Choice Probability Lemmas tile sub  fbbb87d340ca: P2 M Formalism G0 Tops Choice Probability Lemmas tile sub  fbbb87d340ca
-- statement:
--   The P2 M Formalism G0 Tops Choice Probability Lemmas tile sub  fbbb87d340ca construction uses the P2 M Formalism G0 Tops Choice Probability Lemmas tile sub  fbbb87d340ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L306-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L306-L315

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows

theorem P2M_Formalism_G0_TopsChoiceProbabilityLemmas_tile_sub__fbbb87d340ca {n r u s i₀ : ℕ} (hs : s < n / ((6 * r + 1) * u)) (hnot : i₀ ∉ tile r u s) :
    tile r u s ⊆ (range n).erase i₀ := by sorry

alias «Formalism».«G0».«TopsChoiceProbabilityLemmas».«tile_sub'» := P2M_Formalism_G0_TopsChoiceProbabilityLemmas_tile_sub__fbbb87d340ca
