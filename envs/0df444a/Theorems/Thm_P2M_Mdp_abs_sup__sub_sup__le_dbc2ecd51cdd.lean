-- Prove2me | Theorems.Thm_P2M_Mdp_abs_sup__sub_sup__le_dbc2ecd51cdd
-- name    : P2M_Mdp_abs_sup__sub_sup__le_dbc2ecd51cdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:30:11.242726+00:00
-- url     : https://prove2.me/theorems/27ac44be-dfa0-4fca-a50b-9547512618fa
-- title:
--   P2 M Mdp abs sup  sub sup  le dbc2ecd51cdd: P2 M Mdp abs sup  sub sup  le dbc2ecd51cdd
-- statement:
--   If two functions on a nonempty `Finset` are pointwise within `c` of each other, so are their
--       `sup'`s. The general "`sup'` is 1-Lipschitz" fact the contraction proof below needs — proved
--       from scratch (`Finset.le_sup'` / `Finset.sup'_le` only) rather than guessed at from a possibly
--       wrong Mathlib name. Goes via the two one-sided bounds `sup' f ≤ sup' g + c` and
--       `sup' g ≤ sup' f + c` rather than attacking `|sup' f - sup' g| ≤ c` directly, since
--       `Finset.sup'_le`'s conclusion is a plain `≤`, not a subtraction. Corresponds to the role
--       `le_SUP_diff'` plays in `contraction_ℒ` in `MDP_reward.thy`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L51-L67
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L51-L67

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Mdp_Basic
set_option autoImplicit true
open Mdp

theorem P2M_Mdp_abs_sup__sub_sup__le_dbc2ecd51cdd {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f g : ι → ℝ) (c : ℝ)
    (h : ∀ a ∈ s, |f a - g a| ≤ c) :
    |s.sup' hs f - s.sup' hs g| ≤ c := by sorry

alias «Mdp».«abs_sup'_sub_sup'_le» := P2M_Mdp_abs_sup__sub_sup__le_dbc2ecd51cdd
