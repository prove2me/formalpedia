-- Prove2me | Theorems.Thm_ValiantBorder_universalAutomaton
-- name    : ValiantBorder.universalAutomaton
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:06:58.594295+00:00
-- url     : https://prove2.me/theorems/96180e13-2df5-4b73-87f8-29c91367abb2
-- title:
--   A weighted tape automaton for the universal plain sum
-- statement:
--   For each finitely supported assignment of weights in a commutative ring there is one finite weighted tape automaton that computes the universal plain sum on all promised inputs. A common constant times the input size plus the run budget, times its squared binary length, suffices for the tape run.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Universal.lean#L29).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Universal.lean#L29.

import Definitions.Def_ValiantBorder_tapeAutomata

open NS1

theorem ValiantBorder.universalAutomaton {A : Type} [CommRing A] (θ : List Bool → A) (hθ : (Function.support θ).Finite) :
    ∃ (S Γ Q : Type) (_ : Fintype S) (_ : DecidableEq S) (_ : Fintype Γ) (_ : DecidableEq Γ) (_ : Fintype Q)
      (_ : DecidableEq Q) (mu : Nc.Letter S Unit Γ → Matrix Q Q A) (i e : Q) (b0 b1 : Γ) (C : ℕ),
      ∀ (τ : ℕ) (z : Tree) (t : ℕ), Plain θ τ z → C * (z.size + τ) * lg (z.size + τ) ^ 2 ≤ t →
        Nc.runVal mu i e t (fun _ => Nc.Dl.wordG b0 b1 z) = pv θ z := by sorry
