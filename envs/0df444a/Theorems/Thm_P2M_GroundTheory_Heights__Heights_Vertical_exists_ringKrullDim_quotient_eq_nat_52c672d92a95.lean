-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_exists_ringKrullDim_quotient_eq_nat_52c672d92a95
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_exists_ringKrullDim_quotient_eq_nat_52c672d92a95
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:11:52.946942+00:00
-- url     : https://prove2.me/theorems/9928fa49-1a36-4c41-b9c2-9f34390beac2
-- title:
--   P2 M Ground Theory Heights  Heights Vertical exists ring Krull Dim quotient eq nat 52c672d92a95: P2 M Ground Theory Heights  Heights Vertical exists ring Krull Dim quotient eq nat 52c672d92a95
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical exists ring Krull Dim quotient eq nat 52c672d92a95 construction uses the P2 M Ground Theory Heights  Heights Vertical exists ring Krull Dim quotient eq nat 52c672d92a95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PFibreCompDim.lean#L33-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PFibreCompDim.lean#L33-L46

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCompDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFibreCompDim
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
open MvPolynomial IsDedekindDomain
variable {O : Type} [CommRing O] [IsDedekindDomain O] {n : ℕ} (v : HeightOneSpectrum O)
  (W : Ideal (MvPolynomial (Fin n) O))

theorem P2M_GroundTheory_Heights__Heights_Vertical_exists_ringKrullDim_quotient_eq_nat_52c672d92a95 (hWp : W.IsPrime)
    (hW : Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ W) :
    ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) O ⧸ W) = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«exists_ringKrullDim_quotient_eq_nat» := P2M_GroundTheory_Heights__Heights_Vertical_exists_ringKrullDim_quotient_eq_nat_52c672d92a95
