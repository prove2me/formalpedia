-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_form_smul_mem_50a6c960c889
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_form_smul_mem_50a6c960c889
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:06.216872+00:00
-- url     : https://prove2.me/theorems/8e365f7e-7a23-578b-a2b8-69e9dd5b5c98
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum form smul mem 50a6c960c889: P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum form smul mem 50a6c960c889
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum form smul mem 50a6c960c889 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum form smul mem 50a6c960c889 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiltrationHilbSum.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiltrationHilbSum.lean#L50-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiltrationHilbSum
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_form_smul_mem_50a6c960c889 (hM : IsMultigrading ι M piece) {b : K → ℕ} {f : MRing ι F}
    (hf : f ∈ weightedHomogeneousSubmodule F (blockWeight ι) b) {m : K → ℤ} {y : M}
    (hy : y ∈ piece m) : f • y ∈ piece (m + fun k => (b k : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«FiltrationHilbSum».«form_smul_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_form_smul_mem_50a6c960c889
