-- Prove2me | Theorems.Thm_Sensitivity_embed_flipBit_free
-- name    : Sensitivity.embed_flipBit_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:55:35.143375+00:00
-- url     : https://prove2.me/theorems/cdd0bca2-9a90-4f8e-9739-c460bdb2280e
-- title:
--   Sensitivity: embed flip Bit free
-- statement:
--   The Sensitivity construction uses the embed flip Bit free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L30-L40
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L30-L40

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.embed_flipBit_free (free : Finset (Fin n)) (base x : Fin n → Bool)
    (i : Fin n) (hi : i ∈ free) :
    embed free base (flipBit x i) = flipBit (embed free base x) i := by sorry
