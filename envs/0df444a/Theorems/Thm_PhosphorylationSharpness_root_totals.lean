-- Prove2me | Theorems.Thm_PhosphorylationSharpness_root_totals
-- name    : PhosphorylationSharpness.root_totals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:23:37.204806+00:00
-- url     : https://prove2.me/theorems/a68573e1-957e-431b-8780-f41e85a0c327
-- title:
--   Phosphorylation Sharpness: root totals
-- statement:
--   The Phosphorylation Sharpness construction uses the root totals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Assembly.lean#L22-L39
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Assembly.lean#L22-L39

import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Definitions.Def_proofs_PhosphorylationSharpness_Source
import Definitions.Def_proofs_PhosphorylationSharpness_Assembly
set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology BigOperators

theorem PhosphorylationSharpness.root_totals (x r b d : ℝ) (hx : 1 < x) (hd : 0 < d)
    (hrel : (x-1)*(b-r*d)=2*(r-ratio x)*d) :
    ratio x*rootF x*(1+rootS x d*b)=2*r ∧
    rootF x*(1+rootS x d*ratio x*d)=2 ∧
    rootS x d*((1+ratio x)*d)+ratio x*rootS x d*rootF x*(b+d)=2*(r+1) := by sorry
