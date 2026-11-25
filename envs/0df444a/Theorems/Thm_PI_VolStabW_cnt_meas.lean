-- Prove2me | Theorems.Thm_PI_VolStabW_cnt_meas
-- name    : PI.VolStabW.cnt_meas
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:03:27.089819+00:00
-- url     : https://prove2.me/theorems/2f75e3cc-c5bd-4473-8597-b650fd5a012c
-- title:
--   Vol Stab W: cnt meas
-- statement:
--   The Vol Stab W construction uses the cnt meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensCnt.lean#L91-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensCnt.lean#L91-L261

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCnt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {σ : E →ₐ[F] E} (A : AntiB F E σ)
  (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)
variable {K : Type} [CommRing K] [Algebra (𝓞 F ⧸ v.asIdeal) K] (r : K)
  (hr : r * r = algebraMap _ K (red v (algebraMap F (Fv F v) A.D0)))
  (σ' : K ≃ₐ[𝓞 F ⧸ v.asIdeal] K) (hσr : σ' r = -r)
variable (hbij : Function.Bijective
  (fun p : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) => algebraMap _ K p.1 + algebraMap _ K p.2 * r))
include hσr hbij
set_option maxHeartbeats 400000

theorem PI.VolStabW.cnt_meas [Finite K] (hσ : ∀ x, σ (σ x) = x) {M a d : ℕ} [MeasurableAdd (Fin a → Fin M → Fv F v ⊗[F] E)] (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (T : Matrix (Fin a) (Fin a) E)
    (hT : ∀ i j, σ (T j i) = T i j) (b : Module.Basis (Fin d) F E)
    (hbc : ∀ j k, algebraMap F (Fv F v) (b.repr (A.c j) k) ∈ v.adicCompletionIntegers F)
    (hcb : ∀ k j, algebraMap F (Fv F v) (A.c.repr (b k) j) ∈ v.adicCompletionIntegers F)
    (hJi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (J p q) j) ∈ v.adicCompletionIntegers F)
    (hTi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (T p q) j) ∈ v.adicCompletionIntegers F)
    (hNm : MeasurableSet (lamF b v a M 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)))
    (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) [μ.IsAddLeftInvariant] :
    μ (latV b v ∩ gramH (Fv F v) σ hσ J hJ ⁻¹'
          {z | z - hermOf (Fv F v) σ T hT ∈ hF b v σ a 0}) =
        (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K)
          ((entL v A hD J hJi).map (rho v A hD r hr)) X = (entL v A hD T hTi).map (rho v A hD r hr)} : ENNReal) *
          μ (lamF b v a M 0) := by sorry
