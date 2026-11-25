-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locMap_injective_d760537304b0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locMap_injective_d760537304b0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:02.786496+00:00
-- url     : https://prove2.me/theorems/493be088-9ca6-5818-9ec6-200fbefc95c2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Map injective d760537304b0: P2 M Ground Theory Heights  Heights Kleiman loc Map injective d760537304b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Map injective d760537304b0 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Map injective d760537304b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L304-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L304-L310

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
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
universe u v
universe w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
omit [Module S M] [IsScalarTower S (Poly S N) M] [Module S M'] [IsScalarTower S (Poly S N) M']

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locMap_injective_d760537304b0 (f : M →ₗ[Poly S N] M') (hf : Function.Injective f)
    (I : Finset (Fin (N + 1))) : Function.Injective (locMap f I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locMap_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_locMap_injective_d760537304b0
