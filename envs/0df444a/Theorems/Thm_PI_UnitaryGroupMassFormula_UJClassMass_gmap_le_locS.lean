-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_gmap_le_locS
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.gmap_le_locS
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:41:44.625167+00:00
-- url     : https://prove2.me/theorems/62a2e5da-7ec2-40d9-bc89-874f6f2b8c23
-- title:
--   UJClass Mass: gmap le loc S
-- statement:
--   The UJClass Mass construction uses the gmap le loc S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/GmapLeLocS.lean#L62-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/GmapLeLocS.lean#L62-L81

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.gmap_le_locS (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (S : Submonoid (𝓞 E))
    (K : GL (Fin M) E)
    (h : ∀ x ∈ crdOf b L0, ∃ s ∈ S, (algebraMap (𝓞 E) E s) • (K : Matrix (Fin M) (Fin M) E).mulVec x ∈ crdOf b L0) :
    gmap (linOf b K) L0 ≤ locS S L0 := by sorry
