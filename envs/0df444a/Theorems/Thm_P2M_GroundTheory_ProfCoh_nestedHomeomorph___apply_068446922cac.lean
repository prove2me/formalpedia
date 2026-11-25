-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_nestedHomeomorph___apply_068446922cac
-- name    : P2M_GroundTheory_ProfCoh_nestedHomeomorph___apply_068446922cac
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:54:32.439049+00:00
-- url     : https://prove2.me/theorems/1d89f566-f1f8-5a28-8443-3a07729085e1
-- title:
--   P2 M Ground Theory Prof Coh nested Homeomorph   apply 068446922cac: P2 M Ground Theory Prof Coh nested Homeomorph   apply 068446922cac
-- statement:
--   The P2 M Ground Theory Prof Coh nested Homeomorph   apply 068446922cac construction uses the P2 M Ground Theory Prof Coh nested Homeomorph   apply 068446922cac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/BridgeNested.lean#L86-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/BridgeNested.lean#L86-L93

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_BridgeNested
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory TopRep ContRepresentation
universe u v w
variable {k G : Type u} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]
variable (X : TopRep.{u} k G)

theorem P2M_GroundTheory_ProfCoh_nestedHomeomorph___apply_068446922cac (m : ℕ) (g : G) (a : resolutionX X m) (x : Fin m → G) :
    nestedHomeomorph X m ((resolutionX X m).ρ g a) x =
      X.ρ g (nestedHomeomorph X m a fun i => g⁻¹ * x i) := by sorry

alias «GroundTheory».«ProfCoh».«nestedHomeomorph_ρ_apply» := P2M_GroundTheory_ProfCoh_nestedHomeomorph___apply_068446922cac
