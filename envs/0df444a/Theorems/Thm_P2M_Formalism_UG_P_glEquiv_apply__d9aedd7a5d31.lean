-- Prove2me | Theorems.Thm_P2M_Formalism_UG_P_glEquiv_apply__d9aedd7a5d31
-- name    : P2M_Formalism_UG_P_glEquiv_apply__d9aedd7a5d31
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:29:55.516263+00:00
-- url     : https://prove2.me/theorems/3de0ab97-11ec-4664-9da8-a2b6952b79d7
-- title:
--   P2 M Formalism UG P gl Equiv apply  d9aedd7a5d31: P2 M Formalism UG P gl Equiv apply  d9aedd7a5d31
-- statement:
--   The P2 M Formalism UG P gl Equiv apply  d9aedd7a5d31 construction uses the P2 M Formalism UG P gl Equiv apply  d9aedd7a5d31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Bridge.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Bridge.lean#L9-L13

import Definitions.Def_Formalism_SatakeDualWeyl_StatementB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P

theorem P2M_Formalism_UG_P_glEquiv_apply__d9aedd7a5d31 {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (g : GL n K) (x : n → K) : Formalism.UG.glEquiv g x = (g : Matrix n n K) *ᵥ x := by sorry

alias «Formalism».«UG».«P».«glEquiv_apply'» := P2M_Formalism_UG_P_glEquiv_apply__d9aedd7a5d31
