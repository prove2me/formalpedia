-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_mdisc_cons_add_30be52381836
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLeibniz_mdisc_cons_add_30be52381836
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:48:56.58516+00:00
-- url     : https://prove2.me/theorems/d164bec8-1157-406a-84de-8961b01c645c
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Leibniz mdisc cons add 30be52381836: P2 M Ground Theory Heights  Heights Ma Dens Leibniz mdisc cons add 30be52381836
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Leibniz mdisc cons add 30be52381836 construction uses the P2 M Ground Theory Heights  Heights Ma Dens Leibniz mdisc cons add 30be52381836 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L81-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLeibniz
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_MaDensLeibniz_mdisc_cons_add_30be52381836 {n : ℕ} (A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (A + A') B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      mdisc (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
        mdisc (Fin.cons A' B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLeibniz».«mdisc_cons_add» := P2M_GroundTheory_Heights__Heights_MaDensLeibniz_mdisc_cons_add_30be52381836
