-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_apply_d4ac1e5ea45a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_apply_d4ac1e5ea45a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:36.682954+00:00
-- url     : https://prove2.me/theorems/3ec426ae-4257-436e-9127-3e2b4ea45186
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman free Map apply d4ac1e5ea45a: P2 M Ground Theory Heights  Heights Kleiman free Map apply d4ac1e5ea45a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman free Map apply d4ac1e5ea45a construction uses the P2 M Ground Theory Heights  Heights Kleiman free Map apply d4ac1e5ea45a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L168-L170

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
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
open MvPolynomial
noncomputable section
universe u v w w'
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
omit [Module S M] [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_apply_d4ac1e5ea45a {r : ℕ} (g : Fin r → M) (f : Fin r → Poly S N) :
    freeMap S N g f = ∑ j, f j • g j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«freeMap_apply» := P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_apply_d4ac1e5ea45a
