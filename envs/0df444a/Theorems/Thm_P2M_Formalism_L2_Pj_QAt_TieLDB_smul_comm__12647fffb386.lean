-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Pj_QAt_TieLDB_smul_comm__12647fffb386
-- name    : P2M_Formalism_L2_Pj_QAt_TieLDB_smul_comm__12647fffb386
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:36:51.650823+00:00
-- url     : https://prove2.me/theorems/ef94f9d9-3eb1-5042-bf1f-f35b6111077d
-- title:
--   P2 M Formalism L2 Pj QAt Tie LDB smul comm  12647fffb386: P2 M Formalism L2 Pj QAt Tie LDB smul comm  12647fffb386
-- statement:
--   The P2 M Formalism L2 Pj QAt Tie LDB smul comm  12647fffb386 construction uses the P2 M Formalism L2 Pj QAt Tie LDB smul comm  12647fffb386 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDB.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDB.lean#L11-L12

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDB
open Module
variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
  {V : Type*} [AddCommGroup V] [Module A V] [Module (Localization.AtPrime p) V]
  [IsScalarTower A (Localization.AtPrime p) V]

theorem P2M_Formalism_L2_Pj_QAt_TieLDB_smul_comm__12647fffb386 (s : A) (o : Localization.AtPrime p) (v : V) : s • (o • v) = o • (s • v) := by sorry

alias «Formalism».«L2».«Pj».«QAt».«TieLDB».«smul_comm'» := P2M_Formalism_L2_Pj_QAt_TieLDB_smul_comm__12647fffb386
