-- Prove2me | Theorems.Thm_PI_VolStabW_CompGAux_crd_mulVec_mem
-- name    : PI.VolStabW.CompGAux.crd_mulVec_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:44:40.418083+00:00
-- url     : https://prove2.me/theorems/81ebd49d-85fe-4434-baf7-ec012aeecfea
-- title:
--   Comp GAux: crd mul Vec mem
-- statement:
--   The Comp GAux construction uses the crd mul Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/EventuallyStruct.lean#L83-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/EventuallyStruct.lean#L83-L91

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

theorem PI.VolStabW.CompGAux.crd_mulVec_mem (v : HeightOneSpectrum (𝓞 F)) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (m : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) (y : Fin M → Fv F v ⊗[F] E)
    (hm : ∀ i j p, crd b (Fv F v) (m i j) p ∈ v.adicCompletionIntegers F)
    (hy : ∀ j q, crd b (Fv F v) (y j) q ∈ v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (i : Fin M) (k : Fin d) : crd b (Fv F v) ((m.mulVec y) i) k ∈ v.adicCompletionIntegers F := by sorry
