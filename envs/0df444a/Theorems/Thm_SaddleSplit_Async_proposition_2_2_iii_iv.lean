-- Prove2me | Theorems.Thm_SaddleSplit_Async_proposition_2_2_iii_iv
-- name    : SaddleSplit.Async.proposition_2_2_iii_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:30.700365+00:00
-- url     : https://prove2.me/theorems/542804fb-13cf-4784-96c6-ada217bce77c
-- title:
--   Proposition 2.2(iii)–(iv), p. 6 — zeros of the saddle operator give Kuhn–Tucker points; 𝒟 ≠ ∅ ⇔ zer 𝓢 ≠ ∅ ⇔ Z ≠ ∅ ⇒ 𝒫 ≠ ∅
-- statement:
--   Consider the setting of Problem 1.1, the saddle operator $\boldsymbol{\mathcal S}$ of Definition 2.1, the primal solution set $\mathscr P$ of (1.1), the dual solution set $\mathscr D$ of (1.2), and the Kuhn–Tucker set $\mathsf Z\subset\mathcal H\oplus\mathcal G$ of (2.13). Then:
--
--   1. if $\overline{\mathbf x}=(\overline x,\overline y,\overline z,\overline v^*)\in\operatorname{zer}\boldsymbol{\mathcal S}$, then $(\overline x,\overline v^*)\in\mathsf Z$, and $\mathsf Z\subset\mathscr P\times\mathscr D$;
--   2. the nonemptiness conditions are linked by
--   $$\mathscr D\neq\varnothing\iff\operatorname{zer}\boldsymbol{\mathcal S}\neq\varnothing\iff\mathsf Z\neq\varnothing\ \Longrightarrow\ \mathscr P\neq\varnothing.$$
--
--   These relations transfer convergence to a zero of the saddle operator into primal and dual solutions of the original problem, and turn the hypothesis "the dual problem has a solution" into "the saddle operator has a zero".
--
--   **Formalization Note** The standing hypotheses of Problem 1.1 are assumed. Points of $\mathbf X$ are split by the projections `pX`, `pV` onto the first and last blocks.
-- source:
--   Bùi & Combettes, Multivariate monotone inclusions in saddle form, arXiv:2002.06135v3, p. 6, Proposition 2.2(iii)–(iv) (proof pp. 7–8)

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

namespace SaddleSplit.Async
open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

/-- Proposition 2.2(iii)–(iv), p. 6: if `(x̄, ȳ, z̄, v̄*) ∈ zer 𝓢` then `(x̄, v̄*) ∈ Z ⊂ 𝒫 × 𝒟`;
and `𝒟 ≠ ∅ ⇔ zer 𝓢 ≠ ∅ ⇔ Z ≠ ∅ ⇒ 𝒫 ≠ ∅`. -/
theorem proposition_2_2_iii_iv {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    (prob : Problem H G) (hprob : prob.Hyp) :
    (∀ X ∈ zer (saddleOp prob), (pX X, pV X) ∈ ktSet prob) ∧
    ktSet prob ⊆ primalSet prob ×ˢ dualSet prob ∧
    ((dualSet prob).Nonempty ↔ (zer (saddleOp prob)).Nonempty) ∧
    ((zer (saddleOp prob)).Nonempty ↔ (ktSet prob).Nonempty) ∧
    ((ktSet prob).Nonempty → (primalSet prob).Nonempty) := by sorry

end SaddleSplit.Async
