-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_smul_f065e44fd581
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_smul_f065e44fd581
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:15.617548+00:00
-- url     : https://prove2.me/theorems/3d134be5-d03a-4c90-932f-e4b4760c6c29
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum comp smul f065e44fd581: P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum comp smul f065e44fd581
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum comp smul f065e44fd581 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum comp smul f065e44fd581 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiltrationHilbSum.lean#L70-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiltrationHilbSum.lean#L70-L85

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_smul_f065e44fd581 (hM : IsMultigrading ι M piece) [DirectSum.Decomposition piece] {c : K → ℤ}
    {x : M} (hx : x ∈ piece c) (s : MRing ι F) (m : K → ℤ) :
    comp (piece := piece) m (s • x) =
      (∑ d ∈ s.support with (fun k => (Finsupp.weight (blockWeight ι) d k : ℤ)) = m - c,
        monomial d (coeff d s)) • x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«FiltrationHilbSum».«comp_smul» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_smul_f065e44fd581
