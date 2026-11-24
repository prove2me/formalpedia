-- Prove2me | Theorems.Thm_P2M_Erdos1219_Ctx___lt_lam_02132eacf1ef
-- name    : P2M_Erdos1219_Ctx___lt_lam_02132eacf1ef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:49:19.984762+00:00
-- url     : https://prove2.me/theorems/d6b2ec14-34d7-484f-b1e9-2390c44e1efe
-- title:
--   P2 M Erdos1219 Ctx   lt lam 02132eacf1ef: P2 M Erdos1219 Ctx   lt lam 02132eacf1ef
-- statement:
--   The P2 M Erdos1219 Ctx   lt lam 02132eacf1ef construction uses the P2 M Erdos1219 Ctx   lt lam 02132eacf1ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L83-L84
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L83-L84

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Definitions.Def_Erdos1219_Ramsey
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Definitions.Def_Erdos1219_Canonization
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
open Erdos1219.Ctx
variable {V : Type u} (S : Ctx V)

theorem P2M_Erdos1219_Ctx___lt_lam_02132eacf1ef (k : ℕ) : S.μ k < S.lam k := by sorry

alias «Erdos1219».«Ctx».«μ_lt_lam» := P2M_Erdos1219_Ctx___lt_lam_02132eacf1ef
