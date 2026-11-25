-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_incAC_isLocalHom_02e2103e1a9e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_incAC_isLocalHom_02e2103e1a9e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:17.225729+00:00
-- url     : https://prove2.me/theorems/c055f558-87d4-42dc-b3e0-cac843683ce5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent inc AC is Local Hom 02e2103e1a9e: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent inc AC is Local Hom 02e2103e1a9e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent inc AC is Local Hom 02e2103e1a9e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent inc AC is Local Hom 02e2103e1a9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L404-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L404-L430

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
variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]
variable (T : ∀ k, ι k) (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)
include hT

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_incAC_isLocalHom_02e2103e1a9e : IsLocalHom (incAC hPW) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocLaurent».«incAC_isLocalHom» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_incAC_isLocalHom_02e2103e1a9e
