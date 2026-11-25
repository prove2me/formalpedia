-- Prove2me | Theorems.Thm_PI_LocalEndW_mem_pow_smul_top_iff
-- name    : PI.LocalEndW.mem_pow_smul_top_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:34:59.994253+00:00
-- url     : https://prove2.me/theorems/e60c9ca2-e4d0-41cc-8c89-9156cb76b6e9
-- title:
--   Local End W: mem pow smul top iff
-- statement:
--   The Local End W construction uses the mem pow smul top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/HenselRoot.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/HenselRoot.lean#L12-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_HenselRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Filter Topology
open PI PI.LocalEndW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.LocalEndW.mem_pow_smul_top_iff (ϖ : v.adicCompletionIntegers F) (hϖ : ϖ ≠ 0) (n : ℕ)
    (x : v.adicCompletionIntegers F) :
    x ∈ ((Ideal.span {ϖ}) ^ n • ⊤ : Submodule (v.adicCompletionIntegers F) (v.adicCompletionIntegers F)) ↔
      ‖(x : v.adicCompletion F)‖ ≤ ‖(ϖ : v.adicCompletion F)‖ ^ n := by sorry
