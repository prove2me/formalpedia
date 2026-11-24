-- Prove2me | Theorems.Thm_PhosphorylationSharpness_source_from_coefficients
-- name    : PhosphorylationSharpness.source_from_coefficients
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:23:42.075803+00:00
-- url     : https://prove2.me/theorems/ae274bbe-3bf8-49b1-8d97-9fcd059437f5
-- title:
--   Phosphorylation Sharpness: source from coefficients
-- statement:
--   The Phosphorylation Sharpness construction uses the source from coefficients property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Assembly.lean#L41-L72
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Assembly.lean#L41-L72

import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Definitions.Def_proofs_PhosphorylationSharpness_Source
import Definitions.Def_proofs_PhosphorylationSharpness_Assembly
set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology BigOperators

theorem PhosphorylationSharpness.source_from_coefficients {m : ℕ} (B D : ℝ[X])
    (hB : DensePositive B m) (hD : DensePositive D m) (r x : ℝ)
    (hx : 1 < x)
    (hrel : (x-1)*(B.eval (ratio x)-r*D.eval (ratio x))=
      2*(r-ratio x)*D.eval (ratio x)) :
    let A := (1+X)*D
    let t := fun i : Fin (m+2) => A.coeff i
    let b := fun i : Fin (m+1) => B.coeff i
    let d := fun i : Fin (m+1) => D.coeff i
    let z := reconstruct t b d (ratio x) (rootS x (D.eval (ratio x))) (rootF x)
    z.Positive ∧ Equilibrium (realize t b d) z ∧
      totalE z=2*r ∧ totalF z=2 ∧ totalS z=2*(r+1) := by sorry
