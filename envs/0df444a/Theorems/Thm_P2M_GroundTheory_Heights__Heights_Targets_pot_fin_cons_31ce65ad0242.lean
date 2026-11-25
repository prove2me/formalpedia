-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_pot_fin_cons_31ce65ad0242
-- name    : P2M_GroundTheory_Heights__Heights_Targets_pot_fin_cons_31ce65ad0242
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:46.314893+00:00
-- url     : https://prove2.me/theorems/b26aac8c-eb9b-579a-9f83-a1d5a012223e
-- title:
--   P2 M Ground Theory Heights  Heights Targets pot fin cons 31ce65ad0242: P2 M Ground Theory Heights  Heights Targets pot fin cons 31ce65ad0242
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets pot fin cons 31ce65ad0242 construction uses the P2 M Ground Theory Heights  Heights Targets pot fin cons 31ce65ad0242 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PotFinCons.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PotFinCons.lean#L11-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PoincareLelongRegularised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsRegLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAbsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PotFinCons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem P2M_GroundTheory_Heights__Heights_Targets_pot_fin_cons_31ce65ad0242 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} (M : HermLine ι)
    (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«pot_fin_cons» := P2M_GroundTheory_Heights__Heights_Targets_pot_fin_cons_31ce65ad0242
