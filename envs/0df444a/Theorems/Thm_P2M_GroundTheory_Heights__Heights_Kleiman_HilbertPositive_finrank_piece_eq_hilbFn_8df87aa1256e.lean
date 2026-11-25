-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPositive_finrank_piece_eq_hilbFn_8df87aa1256e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPositive_finrank_piece_eq_hilbFn_8df87aa1256e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:40:16.808354+00:00
-- url     : https://prove2.me/theorems/7dd21693-dff3-5cfa-a30d-5e8d3c662e07
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Hilbert Positive finrank piece eq hilb Fn 8df87aa1256e: P2 M Ground Theory Heights  Heights Kleiman Hilbert Positive finrank piece eq hilb Fn 8df87aa1256e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Hilbert Positive finrank piece eq hilb Fn 8df87aa1256e construction uses the P2 M Ground Theory Heights  Heights Kleiman Hilbert Positive finrank piece eq hilb Fn 8df87aa1256e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPositive.lean#L88-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPositive.lean#L88-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegreePos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertDimZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIntersectionRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedHilbertPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PModulesFromPrimes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRankOfSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPositive
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPositive_finrank_piece_eq_hilbFn_8df87aa1256e (y : Fin (N + 1) → Ω) (n : ℕ) :
    (Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℤ) =
      NumbersDVR.hilbFn (primeOfOne (S := k) y) (fun _ => (n : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«HilbertPositive».«finrank_piece_eq_hilbFn» := P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPositive_finrank_piece_eq_hilbFn_8df87aa1256e
