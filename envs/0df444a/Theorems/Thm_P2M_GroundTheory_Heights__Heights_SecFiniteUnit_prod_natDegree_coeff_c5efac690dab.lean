-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SecFiniteUnit_prod_natDegree_coeff_c5efac690dab
-- name    : P2M_GroundTheory_Heights__Heights_SecFiniteUnit_prod_natDegree_coeff_c5efac690dab
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:58:41.198442+00:00
-- url     : https://prove2.me/theorems/c5a71e75-6279-5a54-9f45-84c6d6cf8950
-- title:
--   P2 M Ground Theory Heights  Heights Sec Finite Unit prod nat Degree coeff c5efac690dab: P2 M Ground Theory Heights  Heights Sec Finite Unit prod nat Degree coeff c5efac690dab
-- statement:
--   The P2 M Ground Theory Heights  Heights Sec Finite Unit prod nat Degree coeff c5efac690dab construction uses the P2 M Ground Theory Heights  Heights Sec Finite Unit prod nat Degree coeff c5efac690dab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecFiniteUnit.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecFiniteUnit.lean#L14-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecFiniteUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_AssemblyPartial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecFiniteUnit
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
open MvPolynomial Vertical
noncomputable section
open GroundTheory.Heights₂.Heights.SecFiniteUnit

theorem P2M_GroundTheory_Heights__Heights_SecFiniteUnit_prod_natDegree_coeff_c5efac690dab {R ι : Type*} [CommSemiring R] (s : Finset ι) (f : ι → Polynomial R)
    (D : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ D i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, D i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, D i) = ∏ i ∈ s, (f i).coeff (D i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SecFiniteUnit».«prod_natDegree_coeff» := P2M_GroundTheory_Heights__Heights_SecFiniteUnit_prod_natDegree_coeff_c5efac690dab
