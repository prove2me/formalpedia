-- Prove2me | Theorems.Thm_TarchaBraids_standardPureBraidWord_eval_transport_v2
-- name    : TarchaBraids.standardPureBraidWord_eval_transport_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T22:46:44.495863+00:00
-- url     : https://prove2.me/theorems/f6e4010e-cb81-4529-9150-2a9602ef544c
-- title:
--   Fully qualified classical pure-braid evaluation strand transport
-- statement:
--   The evaluated classical pure-braid word on n+2 strands is the last elementary half-twist conjugating the far-right extension of the old evaluated word. The canonical type fully qualifies the reusable extension map and its basepoint lemma so the strict target checker sees no undeclared short name.
-- source:
--   Tarcha Theorem 3.11; consequence of the accepted finite signed-list transport identity and the accepted naturality of half-twist-word evaluation. Corrected v2 target after exact admission diagnostic for unqualified addU_base in the v1 statement.

import Mathlib
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1
import Definitions.Def_TarchaBraids_strand_extension_v1
import Theorems.Thm_TarchaBraids_standardPureBraidWord_list_transport_v1
import Theorems.Thm_TarchaBraids_strandExtension_braidWord_eval_v2

open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

namespace TarchaBraids

theorem standardPureBraidWord_eval_transport_v2 (n : ℕ) (j : Fin n) :
    FreeGroup.lift
        (fun i : Fin (n + 2 - 1) => halfTwistBraid (n + 2) i)
        (braidWordFree (standardPureBraidWord (n + 1) j.castSucc))
      =
    halfTwistBraid (n + 2) (Fin.last n) *
      (FundamentalGroup.mapOfEq (TarchaBraids.StrandExtension.addU (n + 1))
        (TarchaBraids.StrandExtension.addU_base (n + 1)))
        (FreeGroup.lift
          (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)
          (braidWordFree (standardPureBraidWord n j))) *
      (halfTwistBraid (n + 2) (Fin.last n))⁻¹ := by sorry

end TarchaBraids
