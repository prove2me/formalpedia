-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_mahler_C_mul_prod_3290182d23cd
-- name    : P2M_GroundTheory_Heights__Heights_FibreMahlerForms_mahler_C_mul_prod_3290182d23cd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:55.103162+00:00
-- url     : https://prove2.me/theorems/a87eeeb6-cd83-4d7c-8551-6604cc828e44
-- title:
--   P2 M Ground Theory Heights  Heights Fibre Mahler Forms mahler C mul prod 3290182d23cd: P2 M Ground Theory Heights  Heights Fibre Mahler Forms mahler C mul prod 3290182d23cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Fibre Mahler Forms mahler C mul prod 3290182d23cd construction uses the P2 M Ground Theory Heights  Heights Fibre Mahler Forms mahler C mul prod 3290182d23cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L116-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L116-L128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms
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
open MvPolynomial NumberField TensorProduct ComplexAt
noncomputable section
open GroundTheory.Heights₂.Heights.FibreMahlerForms
variable {d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_FibreMahlerForms_mahler_C_mul_prod_3290182d23cd {ι : Type*} (s : Finset ι) (L : ι → MvPolynomial (Fin 1 × Fin d) ℂ)
    (hL : ∀ q, L q ≠ 0) (a : ℂ) (ha : a ≠ 0) :
    mahler (HermNorm.std d) 1 (C a * ∏ q ∈ s, L q) =
      Real.log ‖a‖ + ∑ q ∈ s, mahler (HermNorm.std d) 1 (L q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FibreMahlerForms».«mahler_C_mul_prod» := P2M_GroundTheory_Heights__Heights_FibreMahlerForms_mahler_C_mul_prod_3290182d23cd
