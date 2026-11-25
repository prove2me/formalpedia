-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_IAT_loc_bound
-- name    : PI.UnitaryGroupMassFormula.IAT.loc_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:43.983336+00:00
-- url     : https://prove2.me/theorems/caceedb3-3e3e-46b4-b0fd-dfa666d8587b
-- title:
--   IAT: loc bound
-- statement:
--   The IAT construction uses the loc bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralityAtPrimeLattices/AwayLoc.lean#L100-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralityAtPrimeLattices/AwayLoc.lean#L100-L125

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralityAtPrimeLattices_AwayLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IAT

theorem PI.UnitaryGroupMassFormula.IAT.loc_bound {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Formalism.L2.GlobalTheoryTheory.Comp.IsLat Λ)
    (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ z ∈ Formalism.L2.Geo.Def.PC.latV v Λ,
      (fun i => inclE (F := F) (v.adicCompletion F) ((N : ℤ) : E) * (M *ᵥ z) i) ∈ Formalism.L2.Geo.Def.PC.latV v Λ := by sorry
