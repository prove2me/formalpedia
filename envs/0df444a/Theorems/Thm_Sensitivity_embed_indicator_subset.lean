-- Prove2me | Theorems.Thm_Sensitivity_embed_indicator_subset
-- name    : Sensitivity.embed_indicator_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:55:49.342512+00:00
-- url     : https://prove2.me/theorems/9526dd0b-6fc9-4bd2-89d2-e827826856a0
-- title:
--   Sensitivity: embed indicator subset
-- statement:
--   Embedding the indicator of T ⊆ S ⊆ free with base = false
--       gives back the indicator of T.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L88-L97
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L88-L97

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.embed_indicator_subset (free S T : Finset (Fin n))
    (hS : S ⊆ free) (hT : T ⊆ S) :
    embed free (fun _ => false) (indicator T) = indicator T := by sorry
