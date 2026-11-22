-- Prove2me | Theorems.Thm_P2M_Formalism_REAL_factorAction_apply__702f0fa4e7c4
-- name    : P2M_Formalism_REAL_factorAction_apply__702f0fa4e7c4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:03:54.342216+00:00
-- url     : https://prove2.me/theorems/bbdbde5b-0fbe-4a82-9d29-da31c1699c42
-- title:
--   P2 M Formalism REAL factor Action apply  702f0fa4e7c4: P2 M Formalism REAL factor Action apply  702f0fa4e7c4
-- statement:
--   The P2 M Formalism REAL factor Action apply  702f0fa4e7c4 construction uses the P2 M Formalism REAL factor Action apply  702f0fa4e7c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L247-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L247-L252

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem P2M_Formalism_REAL_factorAction_apply__702f0fa4e7c4 {j : ℕ} (i : Fin j) (c d : Fin n) (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    factorAction i c d F α = (if (α i).1 = c then F (Function.update α i (d, (α i).2)) else 0) -
      (if (α i).2 = d then F (Function.update α i ((α i).1, c)) else 0) := by sorry

alias «Formalism».«REAL».«factorAction_apply'» := P2M_Formalism_REAL_factorAction_apply__702f0fa4e7c4
