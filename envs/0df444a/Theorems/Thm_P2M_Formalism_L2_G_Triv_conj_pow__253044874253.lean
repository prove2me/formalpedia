-- Prove2me | Theorems.Thm_P2M_Formalism_L2_G_Triv_conj_pow__253044874253
-- name    : P2M_Formalism_L2_G_Triv_conj_pow__253044874253
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:11:11.719288+00:00
-- url     : https://prove2.me/theorems/ed0a8e84-22d1-54d1-afd4-5fe28eb7d242
-- title:
--   P2 M Formalism L2 G Triv conj pow  253044874253: P2 M Formalism L2 G Triv conj pow  253044874253
-- statement:
--   The P2 M Formalism L2 G Triv conj pow  253044874253 construction uses the P2 M Formalism L2 G Triv conj pow  253044874253 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/OneAddPowOfSq.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/OneAddPowOfSq.lean#L15-L17

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureUpperUni
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddPowOfMulSelfEqZero
import Definitions.Def_Lemmata_GeneralBFactLeftTail_Imports
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv

theorem P2M_Formalism_L2_G_Triv_conj_pow__253044874253 {G : Type} [Group G] (a b : G) (n : ℕ) : (a⁻¹ * b * a) ^ n = a⁻¹ * b ^ n * a := by sorry

alias «Formalism».«L2».«G».«Triv».«conj_pow'» := P2M_Formalism_L2_G_Triv_conj_pow__253044874253
