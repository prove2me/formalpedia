-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_lift_frac_3934fd766e28
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_lift_frac_3934fd766e28
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:07:53.935802+00:00
-- url     : https://prove2.me/theorems/7879da40-90ae-57d2-a60e-2e547a997eda
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists lift frac 3934fd766e28: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists lift frac 3934fd766e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists lift frac 3934fd766e28 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists lift frac 3934fd766e28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L73-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L73-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
noncomputable section
variable {S : Type*} [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] {O : Type*} [CommRing O] [Algebra S O]
  [IsLocalization.AtPrime O 𝔪] {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
  {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_lift_frac_3934fd766e28 {I : Chart x} {f s : Poly O N} {e : ℕ} (hf : f.IsHomogeneous e)
    (hs : s ∈ monos I.1) (hse : s.IsHomogeneous e) :
    ∃ t : S, t ∉ 𝔪 ∧ ∃ g s₀ : Poly S N, g.IsHomogeneous e ∧ s₀ ∈ monos I.1 ∧ s₀.IsHomogeneous e ∧
      map (algebraMap S O) g = C (algebraMap S O t) * f ∧
      algebraMap S Ω t * (aeval x f / aeval x s) = aeval x g / aeval x s₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«exists_lift_frac» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_lift_frac_3934fd766e28
