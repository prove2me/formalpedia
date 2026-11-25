-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_div_mem_chartRingI_68ce525af692
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_div_mem_chartRingI_68ce525af692
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:36.11837+00:00
-- url     : https://prove2.me/theorems/293a5bc2-189d-4240-a0a4-a6803aa8a04b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq pow div mem chart Ring I 68ce525af692: P2 M Ground Theory Heights  Heights Kleiman Translate Eq pow div mem chart Ring I 68ce525af692
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq pow div mem chart Ring I 68ce525af692 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq pow div mem chart Ring I 68ce525af692 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L81-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L81-L98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable (S : Type) [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_div_mem_chartRingI_68ce525af692 (x : Fin (N + 1) → Ω) (I : Kleiman.Chart x) (i₀ : Fin (N + 1))
    {s : Poly S N} (hs : s ∈ Kleiman.monos I.1) :
    ∃ e : ℕ, s.IsHomogeneous e ∧ x i₀ ^ e / aeval x s ∈ IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«pow_div_mem_chartRingI» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_div_mem_chartRingI_68ce525af692
