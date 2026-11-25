-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CCA_hd_zsmul
-- name    : ReciprocityTheory.Coh.CCA.hd_zsmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:50:00.33402+00:00
-- url     : https://prove2.me/theorems/3feda6d6-3ddb-402d-9d52-67eee39e0fb9
-- title:
--   CCA: hd zsmul
-- statement:
--   The CCA construction uses the hd zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L219-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L219-L224

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R]

theorem ReciprocityTheory.Coh.CCA.hd_zsmul {V X : Type u} [AddCommGroup V] (n : ℕ) (c : ℤ) (F : (Fin (n + 1) → X) → V) :
    hd n (c • F) = c • hd n F := by sorry
