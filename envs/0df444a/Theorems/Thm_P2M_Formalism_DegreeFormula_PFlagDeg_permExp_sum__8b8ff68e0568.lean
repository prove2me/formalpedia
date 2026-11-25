-- Prove2me | Theorems.Thm_P2M_Formalism_DegreeFormula_PFlagDeg_permExp_sum__8b8ff68e0568
-- name    : P2M_Formalism_DegreeFormula_PFlagDeg_permExp_sum__8b8ff68e0568
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:51.374343+00:00
-- url     : https://prove2.me/theorems/72db7329-cdf5-4bc0-a437-85ced94555ef
-- title:
--   P2 M Formalism Degree Formula PFlag Deg perm Exp sum  8b8ff68e0568: P2 M Formalism Degree Formula PFlag Deg perm Exp sum  8b8ff68e0568
-- statement:
--   The P2 M Formalism Degree Formula PFlag Deg perm Exp sum  8b8ff68e0568 construction uses the P2 M Formalism Degree Formula PFlag Deg perm Exp sum  8b8ff68e0568 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L31-L37

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.DegreeFormula
open Formalism.DegreeFormula.PFlagDeg

theorem P2M_Formalism_DegreeFormula_PFlagDeg_permExp_sum__8b8ff68e0568 {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) :
    ∑ x : ι × Fin N, permExp σ x = dimFl ι N := by sorry

alias «Formalism».«DegreeFormula».«PFlagDeg».«permExp_sum'» := P2M_Formalism_DegreeFormula_PFlagDeg_permExp_sum__8b8ff68e0568
