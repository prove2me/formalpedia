-- Prove2me | Theorems.Thm_ShiTM_iterate_compM_one_simulation
-- name    : ShiTM.iterate_compM_one_simulation
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T21:06:36.464846+00:00
-- url     : https://prove2.me/theorems/3bd48964-3ac8-460e-84e8-9649b1ff4386
-- title:
--   The composite machine reproduces a run of its first component in exactly the same number of steps
-- statement:
--   If the first component, started from a given configuration, is still running at every earlier moment, then after any number of steps the composite machine started from the lifted configuration is in exactly the lift of the configuration the component is in. The number of steps is equal, not merely bounded, which is what makes the result usable for a running-time argument rather than only for a statement about eventual outcomes.
--
--   The hypothesis that the component has not yet halted at each earlier moment is necessary and not a technical convenience. Once the component halts it stays absent forever, whereas the composite instead enters the phase that transfers the first machine's output to the second machine's input, so from that moment the two runs genuinely differ. The conclusion is also given in the form of a reachability-in-time statement, so that runs may be chained end to end.

import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_stepAux_trStmt_one_simulation

set_option autoImplicit false

namespace ShiTM

open Turing.TM2 ShiTM2

theorem iterate_compM_one_simulation (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₁.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₂ : tm₂.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (n : ℕ) (l : tm₁.Λ) (v : tm₁.σ)
    (S : ∀ i, List (tm₁.Γ i))
    (hlive : ∀ j < n, ∃ (l' : tm₁.Λ) (v' : tm₁.σ) (S' : ∀ i, List (tm₁.Γ i)),
        (fun c : Option (Cfg tm₁.Γ tm₁.Λ tm₁.σ) => c.bind (step tm₁.m))^[j]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ))
          = Option.some (⟨Option.some l', v', S'⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ)) :
    (fun c : Option (CompCfg tm₁ tm₂) => c.bind (step (compM tm₁ tm₂ tr dflt)))^[n]
        (Option.some (liftCfg₁ tm₁ tm₂ T w₂ r ⟨Option.some l, v, S⟩))
      = ((fun c : Option (Cfg tm₁.Γ tm₁.Λ tm₁.σ) => c.bind (step tm₁.m))^[n]
          (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ))).map
            (liftCfg₁ tm₁ tm₂ T w₂ r)
  ∧ (∀ c : Cfg tm₁.Γ tm₁.Λ tm₁.σ,
        (fun c : Option (Cfg tm₁.Γ tm₁.Λ tm₁.σ) => c.bind (step tm₁.m))^[n]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ))
          = Option.some c →
        Nonempty (StateTransition.EvalsToInTime (step (compM tm₁ tm₂ tr dflt))
          (liftCfg₁ tm₁ tm₂ T w₂ r ⟨Option.some l, v, S⟩)
          (Option.some (liftCfg₁ tm₁ tm₂ T w₂ r c)) n)) := by
  sorry

end ShiTM
