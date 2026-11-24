-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_map_mem_genericIdeal_iff_0ed5e7f8fd1e
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPartGauss_map_mem_genericIdeal_iff_0ed5e7f8fd1e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:25.210865+00:00
-- url     : https://prove2.me/theorems/426629cd-8c52-4bea-8ca6-9ff248eea315
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Part Gauss map mem generic Ideal iff 0ed5e7f8fd1e: P2 M Ground Theory Heights  Heights Vertical Part Gauss map mem generic Ideal iff 0ed5e7f8fd1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Part Gauss map mem generic Ideal iff 0ed5e7f8fd1e construction uses the P2 M Ground Theory Heights  Heights Vertical Part Gauss map mem generic Ideal iff 0ed5e7f8fd1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L60-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L60-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.VerticalPartGauss
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal coeffGaussNorm)
open ObjectsChow (genericIdeal)
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_VerticalPartGauss_map_mem_genericIdeal_iff_0ed5e7f8fd1e {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d)
    (x : MvPolynomial (Fin n) ℤ) :
    map (Int.castRingHom ℚ) x ∈ genericIdeal P ↔ x ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPartGauss».«map_mem_genericIdeal_iff» := P2M_GroundTheory_Heights__Heights_VerticalPartGauss_map_mem_genericIdeal_iff_0ed5e7f8fd1e
