-- Prove2me | Theorems.Thm_ShiTM_iterate_compM_two_simulation
-- name    : ShiTM.iterate_compM_two_simulation
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T21:58:57.245232+00:00
-- url     : https://prove2.me/theorems/0ffad2aa-2b1b-496f-a74b-6384af3a5bfc
-- title:
--   The composite machine reproduces a run of its second component in exactly the same number of steps
-- statement:
--   If the second component, started from a given configuration, is still running at every earlier moment, then after any number of steps the composite machine started from the lifted configuration sits in exactly the lift of the configuration the component occupies. The step counts are equal rather than merely comparable, which is what allows the result to be used in a running-time argument instead of only for eventual behaviour.
--
--   Unlike the corresponding statement for the first component, the component is permitted to halt at the final moment: its halt is the composite's halt, and the lifting map sends an absent label to an absent label. The hypothesis that it has not halted at any earlier moment is still required, since a component that has halted stays halted while the composite would have to be doing something else. The conclusion is also supplied as a reachability-in-time statement so that the phases of a composite run may be chained together.

import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_stepAux_trStmt_two_simulation

set_option autoImplicit false

namespace ShiTM

open Turing.TM2 ShiTM2

theorem iterate_compM_two_simulation (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₂.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₁ : tm₁.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (n : ℕ) (l : tm₂.Λ) (v : tm₂.σ)
    (S : ∀ i, List (tm₂.Γ i))
    (hlive : ∀ j < n, ∃ (l' : tm₂.Λ) (v' : tm₂.σ) (S' : ∀ i, List (tm₂.Γ i)),
        (fun c : Option (Cfg tm₂.Γ tm₂.Λ tm₂.σ) => c.bind (step tm₂.m))^[j]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ))
          = Option.some (⟨Option.some l', v', S'⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ)) :
    (fun c : Option (CompCfg tm₁ tm₂) => c.bind (step (compM tm₁ tm₂ tr dflt)))^[n]
        (Option.some (liftCfg₂ tm₁ tm₂ T w₁ r ⟨Option.some l, v, S⟩))
      = ((fun c : Option (Cfg tm₂.Γ tm₂.Λ tm₂.σ) => c.bind (step tm₂.m))^[n]
          (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ))).map
            (liftCfg₂ tm₁ tm₂ T w₁ r)
  ∧ (∀ c : Cfg tm₂.Γ tm₂.Λ tm₂.σ,
        (fun c : Option (Cfg tm₂.Γ tm₂.Λ tm₂.σ) => c.bind (step tm₂.m))^[n]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ))
          = Option.some c →
        Nonempty (StateTransition.EvalsToInTime (step (compM tm₁ tm₂ tr dflt))
          (liftCfg₂ tm₁ tm₂ T w₁ r ⟨Option.some l, v, S⟩)
          (Option.some (liftCfg₂ tm₁ tm₂ T w₁ r c)) n)) := by
  sorry

end ShiTM
