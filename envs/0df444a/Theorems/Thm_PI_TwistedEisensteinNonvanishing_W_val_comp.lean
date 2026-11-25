-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_val_comp
-- name    : PI.TwistedEisensteinNonvanishing.W.val_comp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:29:24.88061+00:00
-- url     : https://prove2.me/theorems/267b069d-a259-41b0-bc2f-8b4266a89e00
-- title:
--   W: val comp
-- statement:
--   The W construction uses the val comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L225-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L225-L247

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
variable (P)
variable {P}
variable {q k₀ r c' n' c n kj : ℕ} (hqq : q = qOf P) (h1 : r = kj + c) (h2 : k₀ ≤ kj) (h3 : kj ≤ n)
  (h4 : r ≤ n' + c') (h5 : k₀ ≤ n')
include hqq h1 h2 h3 h4 h5

theorem PI.TwistedEisensteinNonvanishing.W.val_comp (hp : (Ideal.absNorm P.asIdeal).Prime) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c)
    {y : HomE E (n' + c') (n + c)} (hy : CondQ P q k₀ r c' n' c n y) :
    (AYm q k₀ r c' n' c n (g.toLinearMap ∘ₗ y)).map (redP P) =
      (GA k₀ r c n g).map (redP P) * (AYm q k₀ r c' n' c n y).map (redP P) := by sorry
