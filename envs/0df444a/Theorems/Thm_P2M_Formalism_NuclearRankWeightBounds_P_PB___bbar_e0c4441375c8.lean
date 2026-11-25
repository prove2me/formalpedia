-- Prove2me | Theorems.Thm_P2M_Formalism_NuclearRankWeightBounds_P_PB___bbar_e0c4441375c8
-- name    : P2M_Formalism_NuclearRankWeightBounds_P_PB___bbar_e0c4441375c8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:25.184168+00:00
-- url     : https://prove2.me/theorems/0860872f-980c-4500-ab00-da67c30591a4
-- title:
--   P2 M Formalism Nuclear Rank Weight Bounds P PB   bbar e0c4441375c8: P2 M Formalism Nuclear Rank Weight Bounds P PB   bbar e0c4441375c8
-- statement:
--   The P2 M Formalism Nuclear Rank Weight Bounds P PB   bbar e0c4441375c8 construction uses the P2 M Formalism Nuclear Rank Weight Bounds P PB   bbar e0c4441375c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/DescEquivLiftEquiv.lean#L459-L467
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/DescEquivLiftEquiv.lean#L459-L467

import Definitions.Def_Formalism_LogSumExpBounds_StatementC
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DescEquivLiftEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Formalism.NuclearRankWeightBounds.C
variable {RR K : Type*} [CommRing RR] [CommRing K] [Algebra RR K]
variable {m : ℕ}

theorem P2M_Formalism_NuclearRankWeightBounds_P_PB___bbar_e0c4441375c8 (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) (hZ : IsUnit (toK K Z).det)
    (hZ' : IsUnit (toK K (blk Z)).det) :
    (PB Z hZ hZ').π (Submodule.Quotient.mk (Z *ᵥ eN)) = bbar Z := by sorry

alias «Formalism».«NuclearRankWeightBounds».«P».«PB_π_bbar» := P2M_Formalism_NuclearRankWeightBounds_P_PB___bbar_e0c4441375c8
