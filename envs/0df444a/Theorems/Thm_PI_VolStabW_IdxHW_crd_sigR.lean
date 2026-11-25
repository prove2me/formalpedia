-- Prove2me | Theorems.Thm_PI_VolStabW_IdxHW_crd_sigR
-- name    : PI.VolStabW.IdxHW.crd_sigR
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:39:21.4838+00:00
-- url     : https://prove2.me/theorems/689579e0-5991-433f-84ba-9304861b0b08
-- title:
--   Idx HW: crd sig R
-- statement:
--   The Idx HW construction uses the crd sig R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensIdxA.lean#L16-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensIdxA.lean#L16-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxA
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
open scoped TensorProduct
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PI.VolStabW.IdxHW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)

theorem PI.VolStabW.IdxHW.crd_sigR (y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (sigR (Fv F v) σ y) k =
      ∑ l, algebraMap F (Fv F v) (b.repr (σ (b l)) k) *
        (Algebra.TensorProduct.basis (Fv F v) b).repr y l := by sorry
