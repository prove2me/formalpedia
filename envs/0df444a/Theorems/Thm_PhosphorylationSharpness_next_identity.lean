-- Prove2me | Theorems.Thm_PhosphorylationSharpness_next_identity
-- name    : PhosphorylationSharpness.next_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:20:17.087301+00:00
-- url     : https://prove2.me/theorems/ec492357-4a9f-48b3-9126-5d0da407a1a0
-- title:
--   Phosphorylation Sharpness: next identity
-- statement:
--   The Phosphorylation Sharpness construction uses the next identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Recurrence.lean#L71-L76
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Recurrence.lean#L71-L76

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial

theorem PhosphorylationSharpness.next_identity (a b x : ℝ) (p q : ℝ[X]) :
    (x-1)*(nextN a b p q).eval (ratio x) - 2*(nextJ a b p q).eval (ratio x) =
    (x-a)*(x-b)*((x-1)*p.eval (ratio x)-2*q.eval (ratio x)) := by sorry
