-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantFibreBound_exists_poly_0a4987dfdbda
-- name    : P2M_GroundTheory_Heights__Heights_DominantFibreBound_exists_poly_0a4987dfdbda
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:03.33634+00:00
-- url     : https://prove2.me/theorems/74127505-5aa9-493b-b20b-5d8f65aafdda
-- title:
--   P2 M Ground Theory Heights  Heights Dominant Fibre Bound exists poly 0a4987dfdbda: P2 M Ground Theory Heights  Heights Dominant Fibre Bound exists poly 0a4987dfdbda
-- statement:
--   The P2 M Ground Theory Heights  Heights Dominant Fibre Bound exists poly 0a4987dfdbda construction uses the P2 M Ground Theory Heights  Heights Dominant Fibre Bound exists poly 0a4987dfdbda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDominantFibreBound.lean#L42-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDominantFibreBound.lean#L42-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDominantFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDominantFibreBound
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
open MvPolynomial ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_DominantFibreBound_exists_poly_0a4987dfdbda (hG : ComplexSets.GenericProjectionFinite.Statement) {n d : ℕ}
    (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) (hP : P.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ))
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval p)))
    (b : MvPolynomial (Fin n) ℂ ⧸ P) :
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ), g ≠ 0 ∧
      (g.map (aeval (fun i => Ideal.Quotient.mk P (p i))).toRingHom).eval b = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DominantFibreBound».«exists_poly» := P2M_GroundTheory_Heights__Heights_DominantFibreBound_exists_poly_0a4987dfdbda
