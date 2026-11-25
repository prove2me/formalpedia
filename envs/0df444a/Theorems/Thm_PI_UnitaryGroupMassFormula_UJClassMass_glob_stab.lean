-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_glob_stab
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.glob_stab
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:43:18.26329+00:00
-- url     : https://prove2.me/theorems/c01b8ff5-201c-4bb5-81b9-eaf58bc9f38b
-- title:
--   UJClass Mass: glob stab
-- statement:
--   The UJClass Mass construction uses the glob stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/GmapLeLocS.lean#L106-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/GmapLeLocS.lean#L106-L142

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_GmapLeLocS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] {M : ℕ}

theorem PI.UnitaryGroupMassFormula.UJClassMass.glob_stab {F : Type} [Field F] [Algebra F E] (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    {u k : ℕ} (hu : ∀ x ∈ crdOf b L0, ∀ i, IsIntegral ℤ ((u : F) • x i))
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ crdOf b L0)
    (Y : Matrix (Fin M) (Fin M) E) (s : 𝓞 E) (e : Fin M → Fin M → E) (he : ∀ i j, IsIntegral ℤ (e i j))
    (hY : ∀ i j, (algebraMap (𝓞 E) E s) * (Y - 1) i j = ((u * k : ℕ) : E) * e i j)
    {x : Fin M → E} (hx : x ∈ crdOf b L0) : (algebraMap (𝓞 E) E s) • Y.mulVec x ∈ crdOf b L0 := by sorry
