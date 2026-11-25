-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_TotalDegreeLinear_main
-- name    : UpperTheory.Reformulated.B.TotalDegreeLinear.main
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:22.108407+00:00
-- url     : https://prove2.me/theorems/52849028-f6d0-5b97-aff0-60906a98cee0
-- title:
--   Total Degree Linear: main
-- statement:
--   The Total Degree Linear construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TotalDegreeLinear.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TotalDegreeLinear.lean#L38-L46

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TotalDegreeLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.TotalDegreeLinear.main :
    ∀ {ι A B : Type} [inst : Fintype ι] (g h : Matrix ι ι ℂ) (p : UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B),
      MvPolynomial.totalDegree ((UpperTheory.Reformulated.B.TotalDegreeLinear.sub g h : UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B → UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B) p) ≤
        MvPolynomial.totalDegree p := by sorry
