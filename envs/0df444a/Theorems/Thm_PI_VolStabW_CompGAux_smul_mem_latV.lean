-- Prove2me | Theorems.Thm_PI_VolStabW_CompGAux_smul_mem_latV
-- name    : PI.VolStabW.CompGAux.smul_mem_latV
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:44:55.860905+00:00
-- url     : https://prove2.me/theorems/abbf7820-e12a-4d43-b9dc-d59006b55598
-- title:
--   Comp GAux: smul mem lat V
-- statement:
--   The Comp GAux construction uses the smul mem lat V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/EventuallyStruct.lean#L93-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/EventuallyStruct.lean#L93-L102

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_EventuallyStruct
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
open PI.VolStabW.CompGAux
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.VolStabW.FiniteThetaCoordinates
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem PI.VolStabW.CompGAux.smul_mem_latV (v : HeightOneSpectrum (𝓞 F)) {d a : ℕ} (b : Module.Basis (Fin d) F E)
    (h : HA (Fv F v) σ J)
    (hm : ∀ i j p, crd b (Fv F v)
      (((HA.mat (Fv F v) σ J h : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p ∈
        v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (Y : Fin a → Fin M → Fv F v ⊗[F] E) (hY : Y ∈ latV b v) : h • Y ∈ latV b v := by sorry
