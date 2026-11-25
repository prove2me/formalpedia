-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_redHom_ratio_0cab988a2124
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_redHom_ratio_0cab988a2124
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:10:40.918957+00:00
-- url     : https://prove2.me/theorems/9919227c-4a2f-563c-a994-5f05ff6fd545
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict red Hom ratio 0cab988a2124: P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict red Hom ratio 0cab988a2124
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict red Hom ratio 0cab988a2124 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict red Hom ratio 0cab988a2124 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L322-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L322-L329

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_redHom_ratio_0cab988a2124 (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    {j : Fin (N + 1)} (hyj : y j ≠ 0) (i : Fin (N + 1)) :
    redHom hsp hxy hyj (ratio (hxy j hyj) i) = ratio hyj i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenRestrict».«redHom_ratio» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_redHom_ratio_0cab988a2124
