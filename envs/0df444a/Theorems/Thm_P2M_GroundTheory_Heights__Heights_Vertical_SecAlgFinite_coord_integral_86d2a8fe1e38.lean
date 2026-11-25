-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFinite_coord_integral_86d2a8fe1e38
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFinite_coord_integral_86d2a8fe1e38
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:42:33.786796+00:00
-- url     : https://prove2.me/theorems/5b07299c-641b-4727-9f1a-4cf5d8fc4f0d
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec Alg Finite coord integral 86d2a8fe1e38: P2 M Ground Theory Heights  Heights Vertical Sec Alg Finite coord integral 86d2a8fe1e38
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec Alg Finite coord integral 86d2a8fe1e38 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec Alg Finite coord integral 86d2a8fe1e38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecAlgFinite.lean#L40-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecAlgFinite.lean#L40-L132

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecAlgFinite
variable {k E : Type} [Field k] [Field E] [Algebra k E] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFinite_coord_integral_86d2a8fe1e38 (h1 : IncidenceNull.Statement) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → E) (hy : AlgebraicIndependent k y)
    (hg : IsChowForm Q (e + 1) g) (m : Fin n) :
    IsIntegral E (secCoord (Q.map (MvPolynomial.map (algebraMap k E))) y m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecAlgFinite».«coord_integral» := P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFinite_coord_integral_86d2a8fe1e38
