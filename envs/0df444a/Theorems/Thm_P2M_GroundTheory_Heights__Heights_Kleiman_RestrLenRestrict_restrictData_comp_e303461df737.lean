-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_restrictData_comp_e303461df737
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_restrictData_comp_e303461df737
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:44.605885+00:00
-- url     : https://prove2.me/theorems/51e9a314-cc26-418f-bbbc-5f96f3d2f43c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict restrict Data comp e303461df737: P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict restrict Data comp e303461df737
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict restrict Data comp e303461df737 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict restrict Data comp e303461df737 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L255-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L255-L301

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {K' K'' : Type w}
  [Field K'] [Algebra S K'] [Field K''] [Algebra S K''] {N : ℕ}
  {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {z : Fin (N + 1) → K''}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_restrictData_comp_e303461df737 {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {hyz : ∀ i, z i ≠ 0 → y i ≠ 0}
    {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {Q'' : SubSystem S z K''} {r : Ω → K'}
    {r' : K' → K''} (h1 : RestrictData Q hxy Q' r) (h2 : RestrictData Q' hyz Q'' r') :
    RestrictData Q (fun i hi => hxy i (hyz i hi)) Q'' (r' ∘ r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenRestrict».«restrictData_comp» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_restrictData_comp_e303461df737
