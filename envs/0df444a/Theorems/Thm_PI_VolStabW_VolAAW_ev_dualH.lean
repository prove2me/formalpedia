-- Prove2me | Theorems.Thm_PI_VolStabW_VolAAW_ev_dualH
-- name    : PI.VolStabW.VolAAW.ev_dualH
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:15.374831+00:00
-- url     : https://prove2.me/theorems/204ce0c5-4ee1-4171-bbed-3adcc1739a5f
-- title:
--   Vol AAW: ev dual H
-- statement:
--   The Vol AAW construction uses the ev dual H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensVolC.lean#L49-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensVolC.lean#L49-L90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolC
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
open PI.VolStabW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))

theorem PI.VolStabW.VolAAW.ev_dualH [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) :
    ∀ᶠ v in cofinite, {T : HermR (Fv F v) σ a | ∀ S ∈ hermO b v σ a,
      pairHerm (Fv F v) σ a S T ∈ v.adicCompletionIntegers F} = hermO b v σ a := by sorry
