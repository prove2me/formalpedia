-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_monomial_smul_mem_50a714013970
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_monomial_smul_mem_50a714013970
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:21.482614+00:00
-- url     : https://prove2.me/theorems/3c99734e-2055-498a-856f-fb216d30c602
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum monomial smul mem 50a714013970: P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum monomial smul mem 50a71401
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum monomial smul mem 50a714013970 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum monomial smul mem 50a714013970 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiltrationHilbSum.lean#L21-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiltrationHilbSum.lean#L21-L48

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_monomial_smul_mem_50a714013970 (hM : IsMultigrading ι M piece) (d : (Σ k, ι k) →₀ ℕ) (a : F)
    {m : K → ℤ} {y : M} (hy : y ∈ piece m) :
    (monomial d a : MRing ι F) • y ∈
      piece (m + fun k => (Finsupp.weight (blockWeight ι) d k : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«FiltrationHilbSum».«monomial_smul_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_monomial_smul_mem_50a714013970
