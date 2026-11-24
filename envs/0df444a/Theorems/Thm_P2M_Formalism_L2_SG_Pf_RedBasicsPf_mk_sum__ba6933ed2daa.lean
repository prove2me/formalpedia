-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_RedBasicsPf_mk_sum__ba6933ed2daa
-- name    : P2M_Formalism_L2_SG_Pf_RedBasicsPf_mk_sum__ba6933ed2daa
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:27:38.936929+00:00
-- url     : https://prove2.me/theorems/749be79c-0454-43db-976f-43fda1f624a8
-- title:
--   P2 M Formalism L2 SG Pf Red Basics Pf mk sum  ba6933ed2daa: P2 M Formalism L2 SG Pf Red Basics Pf mk sum  ba6933ed2daa
-- statement:
--   The P2 M Formalism L2 SG Pf Red Basics Pf mk sum  ba6933ed2daa construction uses the P2 M Formalism L2 SG Pf Red Basics Pf mk sum  ba6933ed2daa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L89-L91

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedBasicsPf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
attribute [local instance] Ideal.Quotient.field
variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))

theorem P2M_Formalism_L2_SG_Pf_RedBasicsPf_mk_sum__ba6933ed2daa {d : ℕ} (f : Fin d → I.L) :
    (Submodule.Quotient.mk (∑ i, f i) : RedQ I w) = ∑ i, Submodule.Quotient.mk (f i) := by sorry

alias «Formalism».«L2».«SG».«Pf».«RedBasicsPf».«mk_sum'» := P2M_Formalism_L2_SG_Pf_RedBasicsPf_mk_sum__ba6933ed2daa
