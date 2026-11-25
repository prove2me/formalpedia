-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreEquiv_fibreMk_f2523032aa5c
-- name    : P2M_GroundTheory_Heights__Heights_fibreEquiv_fibreMk_f2523032aa5c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:24.351866+00:00
-- url     : https://prove2.me/theorems/916d02b1-879b-404b-99f4-68e1ca494faa
-- title:
--   P2 M Ground Theory Heights  Heights fibre Equiv fibre Mk f2523032aa5c: P2 M Ground Theory Heights  Heights fibre Equiv fibre Mk f2523032aa5c
-- statement:
--   The P2 M Ground Theory Heights  Heights fibre Equiv fibre Mk f2523032aa5c construction uses the P2 M Ground Theory Heights  Heights fibre Equiv fibre Mk f2523032aa5c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FinrankFibreAtOfIsInvertibleSheaf.lean#L160-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FinrankFibreAtOfIsInvertibleSheaf.lean#L160-L168

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FinrankFibreAtOfIsInvertibleSheaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {X : Scheme.{u}} (L : X.Modules)
variable {L}
variable {p : X} {φ : locRing X p →+* ℂ}

theorem P2M_GroundTheory_Heights__Heights_fibreEquiv_fibreMk_f2523032aa5c {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) (c : Via φ) (r : locRing X p) :
    fibreEquiv φ hp he (fibreMk L φ c (r • germM hp e)) = Via.ofComplex φ (φ r) * c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fibreEquiv_fibreMk» := P2M_GroundTheory_Heights__Heights_fibreEquiv_fibreMk_f2523032aa5c
