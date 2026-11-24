-- Prove2me | Theorems.Thm_P2M_GlobalTheory_adicLevelMap___951f147d84c7
-- name    : P2M_GlobalTheory_adicLevelMap___951f147d84c7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:59.993851+00:00
-- url     : https://prove2.me/theorems/36925384-c51f-4fcd-a6d5-cef9fd69145b
-- title:
--   P2 M Global Theory adic Level Map   951f147d84c7: P2 M Global Theory adic Level Map   951f147d84c7
-- statement:
--   The P2 M Global Theory adic Level Map   951f147d84c7 construction uses the P2 M Global Theory adic Level Map   951f147d84c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L191-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L191-L194

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)

theorem P2M_GlobalTheory_adicLevelMap___951f147d84c7 {m n : ℕ} (h : m ≤ n) :
    adicLevelMap I h ≫ adicLevelι I n = adicLevelι I m := by sorry

alias «GlobalTheory».«adicLevelMap_ι» := P2M_GlobalTheory_adicLevelMap___951f147d84c7
