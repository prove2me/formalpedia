-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_eq_twist_18fb89964ed5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_eq_twist_18fb89964ed5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:22:42.790773+00:00
-- url     : https://prove2.me/theorems/e0d0087e-9473-423d-8204-2e28f8009d3c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq mul eq twist 18fb89964ed5: P2 M Ground Theory Heights  Heights Kleiman Translate Eq mul eq twist 18fb89964ed5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq mul eq twist 18fb89964ed5 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq mul eq twist 18fb89964ed5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L321-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L321-L343

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
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_eq_twist_18fb89964ed5 (P Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) :
    (P.sub I).restrictScalars S * (Q.sub I).restrictScalars S = ((P.twist Q).sub I).restrictScalars S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«mul_eq_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_eq_twist_18fb89964ed5
