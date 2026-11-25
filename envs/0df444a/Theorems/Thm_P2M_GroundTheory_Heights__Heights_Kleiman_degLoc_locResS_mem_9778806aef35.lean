-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_degLoc_locResS_mem_9778806aef35
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_degLoc_locResS_mem_9778806aef35
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:33:07.147834+00:00
-- url     : https://prove2.me/theorems/a25f6cd8-4e9c-4f32-bfbc-3b782a9368d7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman deg Loc loc Res S mem 9778806aef35: P2 M Ground Theory Heights  Heights Kleiman deg Loc loc Res S mem 9778806aef35
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman deg Loc loc Res S mem 9778806aef35 construction uses the P2 M Ground Theory Heights  Heights Kleiman deg Loc loc Res S mem 9778806aef35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L274-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L274-L281

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_degLoc_locResS_mem_9778806aef35 (𝓜 : GradedPMod S N M) (c : ℤ) (I J : StdCell N) (h : I.1 ⊆ J.1)
    (x : LocMod S N M I.1) (hx : x ∈ degLoc 𝓜 c I) : locResS I J h x ∈ degLoc 𝓜 c J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«degLoc_locResS_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_degLoc_locResS_mem_9778806aef35
