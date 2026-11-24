-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_apply_c807c9273bfc
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_apply_c807c9273bfc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:56.564471+00:00
-- url     : https://prove2.me/theorems/45d94f14-1098-4d7e-b1a5-26cf793363d5
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum comp apply c807c9273bfc: P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum comp apply c807c9273bfc
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum comp apply c807c9273bfc construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum comp apply c807c9273bfc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiltrationHilbSum.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiltrationHilbSum.lean#L65-L66

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
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_apply_c807c9273bfc [DirectSum.Decomposition piece] (m : K → ℤ) (y : M) :
    comp (piece := piece) m y = (DirectSum.decompose piece y m : M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«FiltrationHilbSum».«comp_apply» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_apply_c807c9273bfc
