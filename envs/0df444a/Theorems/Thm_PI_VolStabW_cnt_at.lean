-- Prove2me | Theorems.Thm_PI_VolStabW_cnt_at
-- name    : PI.VolStabW.cnt_at
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:03:12.932057+00:00
-- url     : https://prove2.me/theorems/4201ea93-3143-485c-87b6-3495b727d89f
-- title:
--   Vol Stab W: cnt at
-- statement:
--   The Vol Stab W construction uses the cnt at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensCnt.lean#L270-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensCnt.lean#L270-L309

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

theorem PI.VolStabW.cnt_at (hσ : ∀ x, σ (σ x) = x) {M a d : ℕ} [MeasurableAdd (Fin a → Fin M → Fv F v ⊗[F] E)] (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (T : Matrix (Fin a) (Fin a) E)
    (hT : ∀ i j, σ (T j i) = T i j) (b : Module.Basis (Fin d) F E)
    (hbc : ∀ j k, algebraMap F (Fv F v) (b.repr (A.c j) k) ∈ v.adicCompletionIntegers F)
    (hcb : ∀ k j, algebraMap F (Fv F v) (A.c.repr (b k) j) ∈ v.adicCompletionIntegers F)
    (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)
    (hDu : Valued.v (algebraMap F (Fv F v) A.D0) = 1)
    (h2 : Valued.v (algebraMap F (Fv F v) 2) = 1)
    (hJi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (J p q) j) ∈ v.adicCompletionIntegers F)
    (hTi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (T p q) j) ∈ v.adicCompletionIntegers F)
    (hNm : MeasurableSet (lamF b v a M 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)))
    (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) [μ.IsAddLeftInvariant] :
    ∃ (k K : Type) (_ : Field k) (_ : Finite k) (_ : CommRing K) (_ : Algebra k K)
      (σ' : K ≃ₐ[k] K) (J' : Matrix (Fin M) (Fin M) K) (T' : Matrix (Fin a) (Fin a) K),
      IsQuadInv k K σ' ∧ (2 : k) ≠ 0 ∧ (∀ i j, σ' (J' j i) = J' i j) ∧
      (∀ u : E, J.det * u = 1 →
        (∀ j, algebraMap F (Fv F v) (A.c.repr u j) ∈ v.adicCompletionIntegers F) →
          IsUnit J'.det) ∧
      (∀ i j, σ' (T' j i) = T' i j) ∧
      (∀ u : E, T.det * u = 1 →
        (∀ j, algebraMap F (Fv F v) (A.c.repr u j) ∈ v.adicCompletionIntegers F) →
          IsUnit T'.det) ∧
      Nat.card k = Nat.card (𝓞 F ⧸ v.asIdeal) ∧
      μ (latV b v ∩ gramH (Fv F v) σ hσ J hJ ⁻¹'
          {z | z - hermOf (Fv F v) σ T hT ∈ hF b v σ a 0}) =
        (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ENNReal) *
          μ (lamF b v a M 0) := by sorry
