-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_IsPFSum_isPF_sum
-- name    : UpperTheory.Reformulated.B.IsPFSum.isPF_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:08.719621+00:00
-- url     : https://prove2.me/theorems/37230902-ca93-4417-9059-4d0c7d1e15e0
-- title:
--   Is PFSum: is PF sum
-- statement:
--   The Is PFSum construction uses the is PF sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsPFSum.lean#L4-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsPFSum.lean#L4-L18

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPF
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.IsPFSum.isPF_sum :
    ∀ {A : Type} [inst : Ring A] [inst_1 : Algebra ℂ A] {ι : Type} (s : Finset ι) {f : ι → ℂ → A},
      (∀ i ∈ s, UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF (f i)) → UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF fun (Y : ℂ) ↦ ∑ i ∈ s, f i Y := by sorry
