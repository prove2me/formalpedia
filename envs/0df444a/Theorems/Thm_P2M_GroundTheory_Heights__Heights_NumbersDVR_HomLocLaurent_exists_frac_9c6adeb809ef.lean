-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_exists_frac_9c6adeb809ef
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_exists_frac_9c6adeb809ef
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:13.702056+00:00
-- url     : https://prove2.me/theorems/11610c25-98eb-4bd8-94fb-52971dea2994
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent exists frac 9c6adeb809ef: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent exists frac 9c6adeb809ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent exists frac 9c6adeb809ef construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent exists frac 9c6adeb809ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L59-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L59-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
variable (P W : Ideal (MRing ι R)) [P.IsPrime]
variable {P W}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_exists_frac_9c6adeb809ef [W.IsPrime] (hPW : P ≤ W) {a : FractionRing (MRing ι R ⧸ P)}
    (ha : a ∈ homLocRing P W) : ∃ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b ∧
      IsMultiHomog g b ∧ g ∉ W ∧ a = fr P f / fr P g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocLaurent».«exists_frac» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_exists_frac_9c6adeb809ef
