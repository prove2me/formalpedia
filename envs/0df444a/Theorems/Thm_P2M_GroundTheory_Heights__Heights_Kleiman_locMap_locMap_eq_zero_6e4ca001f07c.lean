-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locMap_locMap_eq_zero_6e4ca001f07c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locMap_locMap_eq_zero_6e4ca001f07c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:39.233966+00:00
-- url     : https://prove2.me/theorems/afa97d79-6cae-4b81-9920-c7cbf5ba83a2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Map loc Map eq zero 6e4ca001f07c: P2 M Ground Theory Heights  Heights Kleiman loc Map loc Map eq zero 6e4ca001f07c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Map loc Map eq zero 6e4ca001f07c construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Map loc Map eq zero 6e4ca001f07c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L315-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L315-L321

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
variable {M'' : Type w} [AddCommGroup M''] [Module (Poly S N) M''] [Module S M'']
  [IsScalarTower S (Poly S N) M'']

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locMap_locMap_eq_zero_6e4ca001f07c (f : M' →ₗ[Poly S N] M) (g : M →ₗ[Poly S N] M'')
    (hfg : ∀ m, g (f m) = 0) (I : Finset (Fin (N + 1))) (x : LocMod S N M' I) :
    locMap g I (locMap f I x) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locMap_locMap_eq_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_locMap_locMap_eq_zero_6e4ca001f07c
