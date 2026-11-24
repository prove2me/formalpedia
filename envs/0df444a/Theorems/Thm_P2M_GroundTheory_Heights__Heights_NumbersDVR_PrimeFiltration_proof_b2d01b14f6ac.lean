-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PrimeFiltration_proof_b2d01b14f6ac
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PrimeFiltration_proof_b2d01b14f6ac
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:17.250693+00:00
-- url     : https://prove2.me/theorems/21bdbb57-e8f7-4430-90ba-c310acf747e2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Prime Filtration proof b2d01b14f6ac: P2 M Ground Theory Heights  Heights Numbers DVR Prime Filtration proof b2d01b14f6ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Prime Filtration proof b2d01b14f6ac construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Prime Filtration proof b2d01b14f6ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPrimeFiltration.lean#L48-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPrimeFiltration.lean#L48-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPrimeFiltration
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
universe u
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PrimeFiltration_proof_b2d01b14f6ac (h1 : AssociatedMultiHomogPrime.Statement.{u})
    (h2 : FiltrationStepHilb.Statement.{u}) (h3 : FiltrationStepLength.Statement.{u})
    (h4 : ColonMultiHomog.Statement.{u}) : PrimeFiltration.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PrimeFiltration».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PrimeFiltration_proof_b2d01b14f6ac
