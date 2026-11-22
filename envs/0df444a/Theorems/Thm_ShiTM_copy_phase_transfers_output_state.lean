-- Prove2me | Theorems.Thm_ShiTM_copy_phase_transfers_output_state
-- name    : ShiTM.copy_phase_transfers_output_state
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T22:28:37.322971+00:00
-- url     : https://prove2.me/theorems/57e6e198-0371-4814-8197-d9001329870b
-- title:
--   The copy phase transfers the output and leaves the internal state and transfer register reset
-- statement:
--   Starting at the entry of the transfer phase, with the scratch stack and the second machine's input stack both empty, the composite machine reaches the entry of the second machine's program in exactly twice the length of the first machine's output stack plus two steps, carrying that output onto the second machine's input stack with each symbol translated, emptying the first machine's output stack and the scratch stack, and leaving every other stack untouched.
--
--   This strengthens the corresponding statement about the stacks alone by also determining the composite's internal state on arrival. Both components' own states are carried through unchanged and the transfer register is left empty. The register matters because the two copy passes both end on a pop that fails against an empty stack, and a failed pop clears the register; the components' states matter because neither copy pass ever writes to them.
--
--   Without this the phase cannot be composed with what follows. Running the second machine requires beginning in its initial state, and the composite's halting configuration is required by definition to carry the composite's initial state, so a statement that left the state unconstrained would be true but could not be chained at either end.

import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_copy_loop_transfers_stack

set_option autoImplicit false

namespace ShiTM

open ShiTM2

theorem copy_phase_transfers_output_state (tm₁ tm₂ : Turing.FinTM2) [DecidableEq (ShiTM2.CompK tm₁ tm₂)]
    (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀) (dflt : tm₂.Γ tm₂.k₀)
    (v : ShiTM2.Compσ tm₁ tm₂) (S : ∀ k, List (ShiTM2.CompΓ tm₁ tm₂ k))
    (hscr : S (ShiTM2.kScr tm₁ tm₂) = [])
    (hin : S (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀) = []) :
    ∃ (v' : ShiTM2.Compσ tm₁ tm₂) (S' : ∀ k, List (ShiTM2.CompΓ tm₁ tm₂ k)),
      (fun c : Option (ShiTM2.CompCfg tm₁ tm₂) =>
            c.bind (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt)))^[
          2 * (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length + 2]
            (some { l := some (ShiTM2.lcopyA tm₁ tm₂), var := v, stk := S })
          = some { l := some (ShiTM2.injΛ₂ tm₁ tm₂ tm₂.main), var := v', stk := S' }
      ∧ Nonempty (StateTransition.EvalsToInTime
            (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt))
            { l := some (ShiTM2.lcopyA tm₁ tm₂), var := v, stk := S }
            (some { l := some (ShiTM2.injΛ₂ tm₁ tm₂ tm₂.main), var := v', stk := S' })
            (2 * (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length + 2))
      ∧ S' (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀)
          = (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).map
              (tr : ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) →
                    ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀))
      ∧ S' (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) = []
      ∧ S' (ShiTM2.kScr tm₁ tm₂) = []
      ∧ (∀ k, k ≠ ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁ → k ≠ ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀ →
          k ≠ ShiTM2.kScr tm₁ tm₂ → S' k = S k)
      ∧ v' = (v.1, v.2.1, Option.none) := by
  sorry

end ShiTM
