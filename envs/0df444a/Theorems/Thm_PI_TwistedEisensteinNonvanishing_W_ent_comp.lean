-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ent_comp
-- name    : PI.TwistedEisensteinNonvanishing.W.ent_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:15.127795+00:00
-- url     : https://prove2.me/theorems/82a6e30c-dc46-4a5e-80d9-e4ac548fbfcc
-- title:
--   W: ent comp
-- statement:
--   The W construction uses the ent comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L189-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L189-L195

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

theorem PI.TwistedEisensteinNonvanishing.W.ent_comp (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (y : HomE E (n' + c') (n + c)) (p p' : ℕ) (hp : p < n + c) :
    entB q k₀ c' n' c n 0 0 (g.toLinearMap ∘ₗ y) p p' =
      ∑ p'' ∈ Finset.range (n + c), atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p) *
        entB q k₀ c' n' c n 0 0 y p'' p' := by sorry
