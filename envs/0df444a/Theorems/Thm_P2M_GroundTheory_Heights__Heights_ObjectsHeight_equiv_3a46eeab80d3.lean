-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_equiv_3a46eeab80d3
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_equiv_3a46eeab80d3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:33:47.807094+00:00
-- url     : https://prove2.me/theorems/8e7934fe-9b29-4bdb-9187-2705fb635028
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height equiv 3a46eeab80d3: P2 M Ground Theory Heights  Heights Objects Height equiv 3a46eeab80d3
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height equiv 3a46eeab80d3 construction uses the P2 M Ground Theory Heights  Heights Objects Height equiv 3a46eeab80d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L501-L543
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L501-L543

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_equiv_3a46eeab80d3 :
    (∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S),
      (∀ u, (ofPointMatrix S hS).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) ∧
      (∀ y, (ofPointMatrix S hS).dualNorm y = (IndefiniteRowSideFullHecke.ArithBezout.pointMetric S hS).ρ y) ∧
      (∀ u y, fsLog (ofPointMatrix S hS) u y =
        IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u (fun p => y p.2))) ∧
    (∀ (n : ℕ) (h : HermNorm n), ∃ (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S),
      h = ofPointMatrix S hS) ∧
    (∀ n : ℕ, HermNorm.std n = ofPointMatrix 1 isUnit_one) ∧
    (∀ (n k : ℕ) (S : Matrix (Fin n) (Fin n) ℂ), IsUnit S → ∀ h : HermNorm n,
      (∀ u, h.norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) →
        (∀ g : (Fin k × Fin n → ℂ) → ℝ, Measurable g →
          sphereMean h k g = ∫ u, g u ∂IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S k) ∧
        ∀ f : MvPolynomial (Fin k × Fin n) ℂ, mahler h k f = IndefiniteRowSideFullHecke.ArithBezout.chowMean S k f) ∧
    (∀ (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (ι : Type) (f : MvPolynomial ι K),
      gaussNorm v f = ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm (HeightOneSpectrum.adicAbv K v) f) ∧
    (∀ (K : Type) [Field K] [NumberField K] (ι : Type) (f : MvPolynomial ι K),
      ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f) =
        ∑ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
          Real.log (ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm v.1 f)) ∧
    (∀ (ι : Type) (f : MvPolynomial ι ℚ), IndefiniteRowSideFullHecke.ArithBezout.finGaussLog f =
      ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), Real.log (gaussNorm v f)) ∧
    (∀ (n e δ : ℕ) (H : ArchData ℚ n) (S : Matrix (Fin n) (Fin n) ℂ), IsUnit S →
      (∀ σ u, (H.normAt σ).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) →
        ∀ f : MvPolynomial (Fin (e + 1) × Fin n) ℚ,
          chowHt H (e + 1) δ f = IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ) ∧
    (∀ (K : Type) [Field K] [NumberField K] (n e δ : ℕ) (H : ArchData K n)
      (S : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ w, IsUnit (S w)) →
      (∀ w u, (H.normAt w.embedding).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm (S w) u) →
        ∀ f : MvPolynomial (Fin (e + 1) × Fin n) K,
          chowHt H (e + 1) δ f =
            ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) f δ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«equiv» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_equiv_3a46eeab80d3
