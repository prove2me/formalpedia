-- Prove2me | Theorems.Thm_ValuativeSYZ_lemma_3_5_ctransform_nonexpansive
-- name    : ValuativeSYZ.lemma_3_5_ctransform_nonexpansive
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T11:37:45.774852+00:00
-- url     : https://prove2.me/theorems/5a58759b-7c97-4874-87ca-5923569053b4
-- title:
--   Lemma 3.5 (ii): the $c$-transform is non-expansive in $L^\infty$
-- statement:
--   **Lemma 3.5, second part.** The $c$-transform is non-expansive for the sup-norm: if two bounded
--   functions $\varphi, \psi$ on $X$ satisfy $\lVert \varphi - \psi\rVert_{L^\infty} \le E$, then
--   $$\lVert \varphi^{c} - \psi^{c}\rVert_{L^\infty} \;\le\; E .$$
--   This is what makes $P_c$ closed in the uniform topology, which is used when approximating
--   semipositive potentials by Fubini–Study potentials.
-- source:
--   Yang Li, *Valuative independence and metric SYZ conjecture*, arXiv:2605.00516v1 (1 May 2026), https://arxiv.org/abs/2605.00516, pp. 15, Lemma 3.5 (second assertion)

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

set_option autoImplicit false

open MeasureTheory

namespace ValuativeSYZ

/-- **Lemma 3.5 (second part).** The `c`-transform is non-expansive for the sup-norm. -/
theorem lemma_3_5_ctransform_nonexpansive {X B : Type*} [Nonempty X]
    (c : X → B → ℝ) (φ ψ : X → ℝ) (M E : ℝ)
    (hc : ∀ x p, |c x p| ≤ M) (hφ : ∀ x, |φ x| ≤ M) (hψ : ∀ x, |ψ x| ≤ M)
    (hE : ∀ x, |φ x - ψ x| ≤ E) (p : B) :
    |ctransform c φ p - ctransform c ψ p| ≤ E := by sorry

end ValuativeSYZ
