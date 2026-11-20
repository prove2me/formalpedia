-- Prove2me | Theorems.Thm_Sensitivity_embed_flipBit_nonfree
-- name    : Sensitivity.embed_flipBit_nonfree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:55:37.617288+00:00
-- url     : https://prove2.me/theorems/396d70f3-8501-43b4-bea7-7d666e771bfd
-- title:
--   Sensitivity: embed flip Bit nonfree
-- statement:
--   The Sensitivity construction uses the embed flip Bit nonfree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L42-L49
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean#L42-L49

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
set_option autoImplicit false
open Sensitivity
variable {n : ℕ}

theorem Sensitivity.embed_flipBit_nonfree (free : Finset (Fin n)) (base x : Fin n → Bool)
    (i : Fin n) (hi : i ∉ free) :
    embed free base (flipBit x i) = embed free base x := by sorry
