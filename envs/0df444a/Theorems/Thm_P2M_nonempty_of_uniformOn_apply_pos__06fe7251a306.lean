-- Prove2me | Theorems.Thm_P2M_nonempty_of_uniformOn_apply_pos__06fe7251a306
-- name    : P2M_nonempty_of_uniformOn_apply_pos__06fe7251a306
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:37:37.90663+00:00
-- url     : https://prove2.me/theorems/4ea015d6-8348-4b3b-9faa-538708c3bae2
-- title:
--   P2 M nonempty of uniform On apply pos  06fe7251a306: P2 M nonempty of uniform On apply pos  06fe7251a306
-- statement:
--   The P2 M nonempty of uniform On apply pos  06fe7251a306 construction uses the P2 M nonempty of uniform On apply pos  06fe7251a306 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L135-L140
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L135-L140

import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNRat.Floor
import Mathlib.Tactic.Rify
import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_Compactness
import Definitions.Def_Polychromatic_LocalLemma
import Definitions.Def_Polychromatic_Existence
set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory

theorem P2M_nonempty_of_uniformOn_apply_pos__06fe7251a306 {Ω : Type*} [MeasurableSpace Ω] {s t : Set Ω}
    (h : 0 < uniformOn s t) (hs : MeasurableSet s) :
    (s ∩ t).Nonempty := by sorry

alias «nonempty_of_uniformOn_apply_pos'» := P2M_nonempty_of_uniformOn_apply_pos__06fe7251a306
