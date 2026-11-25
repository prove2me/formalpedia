-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_row_tr
-- name    : PI.TwistedEisensteinNonvanishing.W.row_tr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:49.247831+00:00
-- url     : https://prove2.me/theorems/32bfeb75-d122-4ae9-b064-7564f96add11
-- title:
--   W: row tr
-- statement:
--   The W construction uses the row tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L90-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L90-L115

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

theorem PI.TwistedEisensteinNonvanishing.W.row_tr {N' n c k₀ : ℕ} (hk : k₀ ≤ n) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (y : HomE E N' (n + c))
    (s p : ℕ) (hp : p < n + c) :
    atN ((g.toLinearMap ∘ₗ y) (eN E N' s)) (fIdx k₀ c n p) =
      ∑ p'' ∈ Finset.range (n + c), atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p) *
        atN (y (eN E N' s)) (fIdx k₀ c n p'') := by sorry
