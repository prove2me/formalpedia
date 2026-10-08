-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_no_strict_scalar_lower_bound_of_eventual_failure
-- name    : WeilDefect.MarkerStability.no_strict_scalar_lower_bound_of_eventual_failure
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T21:28:43.491837+00:00
-- url     : https://prove2.me/theorems/e2a3f26c-f234-4f4c-9325-0fafc03c753e
-- title:
--   A norm limit cannot gain a strict scalar lower margin above an eventually failed threshold
-- statement:
--   Let $K$ be a complex Hilbert space, let $F_i$ be bounded operators converging in operator norm along a nontrivial filter to a self-adjoint operator $A$, and suppose $F_i$ are eventually self-adjoint. If $bI\nleq F_i$ eventually, then for every $a>b$, $$aI\nleq A.$$ The threshold $bI\le A$ itself may still hold. In the companion native Connes development this applies to the existing ordered support-right limit on the unchanged actual-quartet coefficient space, ruling out a strict margin above one half at the last inner half-bound window. It does not prove the endpoint half-bound or RH.
-- source:
--   monocap-tech/weil, Screening/MarkerThresholdBoundary.lean, with actual-quartet application in Connes/EndpointHalfBoundary.lean. This operator-topology support theorem changes no native zero configuration, test class, selected packet or physical carrier. The existing scalar norm-close helper is reproduced as a private complete lemma for independent checking.

import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ComplexOrder Topology
open ContinuousLinearMap Filter Set
noncomputable section
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private lemma scalar_lower_of_norm_close (A B : K →L[ℂ] K)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (a η : ℝ)
    (ha : a • (1 : K →L[ℂ] K) ≤ A) (hη : ‖A - B‖ ≤ η) :
    (a - η) • (1 : K →L[ℂ] K) ≤ B := by
  have hd := IsSelfAdjoint.le_algebraMap_norm_self (hA.sub hB)
  have he : A - B ≤ η • (1 : K →L[ℂ] K) := hd.trans (by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      smul_le_smul_of_nonneg_right hη (zero_le_one : (0 : K →L[ℂ] K) ≤ 1))
  rw [sub_smul]
  exact sub_le_iff_le_add.mpr (by
    simpa only [add_comm] using ha.trans (sub_le_iff_le_add.mp he))

private lemma scalar_identity_mono {a b : ℝ} (hab : a ≤ b) :
    a • (1 : K →L[ℂ] K) ≤ b • 1 :=
  smul_le_smul_of_nonneg_right hab zero_le_one

theorem WeilDefect.MarkerStability.no_strict_scalar_lower_bound_of_eventual_failure
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (F : ι → K →L[ℂ] K) (A : K →L[ℂ] K) (b a : ℝ)
    (hlim : Tendsto F l (nhds A)) (hA : IsSelfAdjoint A)
    (hself : ∀ᶠ i in l, IsSelfAdjoint (F i))
    (hbad : ∀ᶠ i in l, ¬ b • (1 : K →L[ℂ] K) ≤ F i)
    (hba : b < a) : ¬ a • (1 : K →L[ℂ] K) ≤ A := by sorry
