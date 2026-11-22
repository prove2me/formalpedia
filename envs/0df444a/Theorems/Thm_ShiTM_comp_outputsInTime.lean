-- Prove2me | Theorems.Thm_ShiTM_comp_outputsInTime
-- name    : ShiTM.comp_outputsInTime
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-15T00:07:15.554006+00:00
-- url     : https://prove2.me/theorems/00e1a196-286b-4a3d-a968-4f56c9a58229
-- title:
--   The sequential composite of two multi-stack machines computes the composition, in the sum of their times plus the transfer cost
-- statement:
--   Suppose the first machine, given an input, outputs an intermediate value within some number of steps, and the second machine, given that intermediate value with its symbols translated into the second machine's input alphabet, outputs a final value within some number of steps. Then the sequential composite of the two machines, given the original input, outputs that final value within the sum of the two step counts plus twice the length of the intermediate value plus two.
--
--   The additional cost is the transfer between the two machines. A multi-stack machine that has halted takes no further steps, so a composite cannot simply run one machine and then the other; the first machine's halt instruction is replaced by a jump into a copy phase, which moves its output onto the second machine's input stack through a scratch stack. Two passes are needed because a single pass reverses the order, and each pass costs one step per symbol together with a final step for the failed pop that detects the empty stack.
--
--   The statement is the form required to compose machines at all, and it is stated for arbitrary machines rather than for any particular pair. It asserts existence of a run rather than exhibiting one, because the notion of outputting within a given time is data rather than a proposition; that is also the form the intended application takes, since polynomial-time computability is itself stated as the existence of such a machine.

import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_initList_haltList_laws
import Theorems.Thm_ShiTM_initList_haltList_comp
import Theorems.Thm_ShiTM_iterate_compM_one_simulation
import Theorems.Thm_ShiTM_iterate_compM_two_simulation
import Theorems.Thm_ShiTM_copy_phase_transfers_output_state

set_option autoImplicit false

namespace ShiTM

open ShiTM2

theorem comp_outputsInTime (tm₁ tm₂ : Turing.FinTM2) [inst : DecidableEq (ShiTM2.CompK tm₁ tm₂)]
    (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀) (dflt : tm₂.Γ tm₂.k₀)
    (s : List (tm₁.Γ tm₁.k₀)) (t : List (tm₁.Γ tm₁.k₁)) (u : List (tm₂.Γ tm₂.k₁))
    (m₁ m₂ : ℕ)
    (h₁ : Turing.TM2OutputsInTime tm₁ s (Option.some t) m₁)
    (h₂ : Turing.TM2OutputsInTime tm₂ (t.map tr) (Option.some u) m₂) :
    Nonempty (Turing.TM2OutputsInTime (ShiTM2.comp tm₁ tm₂ tr dflt) s (Option.some u)
      (m₁ + (2 * t.length + 2) + m₂)) := by
  sorry

end ShiTM
