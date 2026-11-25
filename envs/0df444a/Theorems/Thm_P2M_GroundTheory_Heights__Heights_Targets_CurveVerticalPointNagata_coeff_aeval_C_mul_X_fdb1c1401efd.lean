-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_coeff_aeval_C_mul_X_fdb1c1401efd
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_coeff_aeval_C_mul_X_fdb1c1401efd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:05:34.215915+00:00
-- url     : https://prove2.me/theorems/8808cf10-799e-5cb2-bd3a-e43c80d20671
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata coeff aeval C mul X fdb1c1401efd: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata coeff aeval C mul X fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata coeff aeval C mul X fdb1c1401efd construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata coeff aeval C mul X fdb1c1401efd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointNagata.lean#L62-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointNagata.lean#L62-L85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointNagata
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointNagata
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_coeff_aeval_C_mul_X_fdb1c1401efd {S : Type*} [CommRing S] [Algebra ℤ S] [Algebra ℤ (MvPolynomial K S)] (r : (Σ k, ι k) → S) (f : MRing ι) (n : K →₀ ℕ) :
    (aeval (fun p => MvPolynomial.C (r p) * MvPolynomial.X p.1) f : MvPolynomial K S).coeff n =
      aeval r (comp (⇑n) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointNagata».«coeff_aeval_C_mul_X» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_coeff_aeval_C_mul_X_fdb1c1401efd
