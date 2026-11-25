-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_mem_iSup_inf_ffae419b65de
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_mem_iSup_inf_ffae419b65de
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:05.054803+00:00
-- url     : https://prove2.me/theorems/781ecc45-4d64-4010-b9cf-b2673c477cc6
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot mem i Sup inf ffae419b65de: P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot mem i Sup inf ffae419b65de
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot mem i Sup inf ffae419b65de construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot mem i Sup inf ffae419b65de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L122-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L122-L142

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGradedSubquot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_mem_iSup_inf_ffae419b65de {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {N : Submodule (MRingOver S ι) M}
    (hHN : Submodule.span (MRingOver S ι) H ≤ N) (x : N) (hx : (x : M) ∈ Submodule.span (MRingOver S ι) H) :
    x ∈ ⨆ c, ((Submodule.span (MRingOver S ι) H).comap N.subtype).restrictScalars S ⊓ subGrading 𝓜 N c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GradedSubquot».«mem_iSup_inf» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_mem_iSup_inf_ffae419b65de
