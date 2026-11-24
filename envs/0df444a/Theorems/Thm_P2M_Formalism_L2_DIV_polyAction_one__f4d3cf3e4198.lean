-- Prove2me | Theorems.Thm_P2M_Formalism_L2_DIV_polyAction_one__f4d3cf3e4198
-- name    : P2M_Formalism_L2_DIV_polyAction_one__f4d3cf3e4198
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:56.868248+00:00
-- url     : https://prove2.me/theorems/b9d6d18f-5ad7-4e40-9783-89a185cef395
-- title:
--   P2 M Formalism L2 DIV poly Action one  f4d3cf3e4198: P2 M Formalism L2 DIV poly Action one  f4d3cf3e4198
-- statement:
--   The P2 M Formalism L2 DIV poly Action one  f4d3cf3e4198 construction uses the P2 M Formalism L2 DIV poly Action one  f4d3cf3e4198 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L600-L601
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L600-L601

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
omit [NumberField K]

theorem P2M_Formalism_L2_DIV_polyAction_one__f4d3cf3e4198 (lam : ι → DomWeight n) (F : Pol K ι n) : actP lam 1 F = F := by sorry

alias «Formalism».«L2».«DIV».«polyAction_one₂» := P2M_Formalism_L2_DIV_polyAction_one__f4d3cf3e4198
