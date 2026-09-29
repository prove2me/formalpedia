-- Prove2me | Theorems.Thm_ValuativeSYZ_lemma_3_5_ctransform_involutive
-- name    : ValuativeSYZ.lemma_3_5_ctransform_involutive
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T11:44:05.453771+00:00
-- url     : https://prove2.me/theorems/c0b0f986-c42d-4003-96b7-08f666de7b34
-- title:
--   Lemma 3.5 (iii): the $c$-transform is involutive on its image
-- statement:
--   **Lemma 3.5, third part.** On the image of the $c$-transform the transform is involutive: if
--   $\varphi = \psi^{c}$ for some bounded $\psi$ on $B$ — that is, if $\varphi$ belongs to the class
--   $P_c$ — then
--   $$(\varphi^{c})^{c} \;=\; \varphi .$$
--   Combined with the previous lemma this identifies $P_c$ with the set of fixed points of the double
--   transform, which is the form in which the class is used in §3.3 and §4.
-- source:
--   Yang Li, *Valuative independence and metric SYZ conjecture*, arXiv:2605.00516v1 (1 May 2026), https://arxiv.org/abs/2605.00516, pp. 15, Lemma 3.5 (third assertion, definition of $P_c$)

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

set_option autoImplicit false

open MeasureTheory

namespace ValuativeSYZ

/-- **Lemma 3.5 (third part).** On the image of the `c`-transform — the class `P_c` — the
`c`-transform is involutive. -/
theorem lemma_3_5_ctransform_involutive {X B : Type*} [Nonempty X] [Nonempty B]
    (c : X → B → ℝ) (M : ℝ) (hc : ∀ x p, |c x p| ≤ M)
    (φ : X → ℝ) (hφ : φ ∈ Pc c) :
    ctransformDual c (ctransform c φ) = φ := by sorry

end ValuativeSYZ
