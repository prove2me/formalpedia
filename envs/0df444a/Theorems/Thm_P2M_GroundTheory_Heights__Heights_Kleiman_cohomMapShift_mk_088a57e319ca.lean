-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cohomMapShift_mk_088a57e319ca
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_cohomMapShift_mk_088a57e319ca
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:58.255468+00:00
-- url     : https://prove2.me/theorems/9cc7d838-6e1c-4e7b-a17f-7c12e30f7e7e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman cohom Map Shift mk 088a57e319ca: P2 M Ground Theory Heights  Heights Kleiman cohom Map Shift mk 088a57e319ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman cohom Map Shift mk 088a57e319ca construction uses the P2 M Ground Theory Heights  Heights Kleiman cohom Map Shift mk 088a57e319ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreFree.lean#L114-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreFree.lean#L114-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
variable (𝓜 : GradedPMod S N M) {r : ℕ} (b : Module.Basis (Fin r) (Poly S N) M) (d : Fin r → ℤ)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_cohomMapShift_mk_088a57e319ca {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : M →ₗ[Poly S N] M')
    (t : ℤ) (hf : ∀ (a : ℤ) (m : M), m ∈ 𝓜.piece a → f m ∈ 𝓜'.piece (a + t)) (i : ℕ) {c c' : ℤ}
    (hc : c' = c + t) (z : Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS i) :
    ∃ z' : Cech.cocyDeg (locSys S N M') (degLoc 𝓜' c') locResS i,
      cohomMapShift f t hf i hc (Submodule.Quotient.mk z : cohom 𝓜 i c) =
        (Submodule.Quotient.mk z' : cohom 𝓜' i c') ∧ ∀ I, z'.1 I = locMap f I.1.1 (z.1 I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«cohomMapShift_mk» := P2M_GroundTheory_Heights__Heights_Kleiman_cohomMapShift_mk_088a57e319ca
