-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_ev_comp_psiQ_1dd9a2bf17de
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_ev_comp_psiQ_1dd9a2bf17de
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:15.887231+00:00
-- url     : https://prove2.me/theorems/667197f2-1df4-4773-8592-5e6a44c3766f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent ev comp psi Q 1dd9a2bf17de: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent ev comp psi Q 1dd9a2bf17de
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent ev comp psi Q 1dd9a2bf17de construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent ev comp psi Q 1dd9a2bf17de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L245-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L245-L251

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
variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime] (T : ∀ k, ι k)
  (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_ev_comp_psiQ_1dd9a2bf17de (hPh : IsMultiHomogIdeal P) :
    (ev T hPW hT).comp (psiQ T hPW hT hPh) =
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocLaurent».«ev_comp_psiQ» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_ev_comp_psiQ_1dd9a2bf17de
