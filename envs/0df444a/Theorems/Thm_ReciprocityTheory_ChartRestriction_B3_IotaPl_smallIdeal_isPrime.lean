-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_B3_IotaPl_smallIdeal_isPrime
-- name    : ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal_isPrime
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:03:07.454264+00:00
-- url     : https://prove2.me/theorems/37482c8d-af18-4f1d-8558-727e86eebed7
-- title:
--   Iota Pl: small Ideal is Prime
-- statement:
--   The Iota Pl construction uses the small Ideal is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/LatticeEmbeddings/IotaPlace.lean#L76-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/LatticeEmbeddings/IotaPlace.lean#L76-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlaceB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.B3 ReciprocityTheory.ChartRestriction.B3.IotaPl
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal_isPrime (ι : K →+* ℂ_[p]) : (smallIdeal ι).IsPrime := by sorry
