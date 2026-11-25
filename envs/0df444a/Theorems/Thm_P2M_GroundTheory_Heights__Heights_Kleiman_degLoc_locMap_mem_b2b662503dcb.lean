-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_degLoc_locMap_mem_b2b662503dcb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_degLoc_locMap_mem_b2b662503dcb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:50.372424+00:00
-- url     : https://prove2.me/theorems/090edf7a-3cc7-4e69-b843-ebc428407af3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman deg Loc loc Map mem b2b662503dcb: P2 M Ground Theory Heights  Heights Kleiman deg Loc loc Map mem b2b662503dcb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman deg Loc loc Map mem b2b662503dcb construction uses the P2 M Ground Theory Heights  Heights Kleiman deg Loc loc Map mem b2b662503dcb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L283-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L283-L293

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_degLoc_locMap_mem_b2b662503dcb {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : GradedHom 𝓜 𝓜')
    (c : ℤ) (I : StdCell N) (x : LocMod S N M I.1) (hx : x ∈ degLoc 𝓜 c I) :
    locMap f.toLin I.1 x ∈ degLoc 𝓜' c I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«degLoc_locMap_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_degLoc_locMap_mem_b2b662503dcb
