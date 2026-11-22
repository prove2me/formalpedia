-- Prove2me | Theorems.Thm_P2M_Formalism_L2_DIV_isCMSub_cmMax__3b92c5b81347
-- name    : P2M_Formalism_L2_DIV_isCMSub_cmMax__3b92c5b81347
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:29.854059+00:00
-- url     : https://prove2.me/theorems/af6b0cd2-801e-4d83-9b82-3a02d9f896cb
-- title:
--   P2 M Formalism L2 DIV is CMSub cm Max  3b92c5b81347: P2 M Formalism L2 DIV is CMSub cm Max  3b92c5b81347
-- statement:
--   The P2 M Formalism L2 DIV is CMSub cm Max  3b92c5b81347 construction uses the P2 M Formalism L2 DIV is CMSub cm Max  3b92c5b81347 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L317-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L317-L317

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_L2_DIV_isCMSub_cmMax__3b92c5b81347 : IsCMSub (cmMax K) := by sorry

alias «Formalism».«L2».«DIV».«isCMSub_cmMax'» := P2M_Formalism_L2_DIV_isCMSub_cmMax__3b92c5b81347
