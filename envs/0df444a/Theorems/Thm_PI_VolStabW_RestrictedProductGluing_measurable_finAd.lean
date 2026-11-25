-- Prove2me | Theorems.Thm_PI_VolStabW_RestrictedProductGluing_measurable_finAd
-- name    : PI.VolStabW.RestrictedProductGluing.measurable_finAd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:49.952095+00:00
-- url     : https://prove2.me/theorems/b5cf1ca7-1082-5025-974a-808784456b2d
-- title:
--   Restricted Product Gluing: measurable fin Ad
-- statement:
--   The Restricted Product Gluing construction uses the measurable fin Ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/RPGlue.lean#L94-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/RPGlue.lean#L94-L117

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RPGlue
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct RestrictedProduct
open PI.VolStabW.RestrictedProductGluing
open PositiveNearLattice
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {M a d : ℕ} (b : Module.Basis (Fin d) F E)

theorem PI.VolStabW.RestrictedProductGluing.measurable_finAd (i : Fin a) (j : Fin M) (k : Fin d) :
    Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => finAd b p i j k) := by sorry
