-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_Supplement_lemma_3_9
-- name    : TarskiBootstrap.Dimensional.Supplement.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:09:33.107202+00:00
-- url     : https://prove2.me/theorems/8cb2d982-e499-45bc-a2cc-7eca8ab4535f
-- title:
--   Lemma 3.9 — Properties of the antichain constructor
-- statement:
--   Let $\mathcal F$ be a family of monotone self-maps of $[n]^k$, each with a unique fixed point. With $\mathcal B(f)(x,y)=(f(x),\overline{f(\bar y)})$:
--
--   1. every function in $\mathcal B(\mathcal F)$ is monotone and has a unique fixed point, and the set of all possible fixed points of $\mathcal B(\mathcal F)$ is an antichain;
--   2. $\mathcal B$ preserves equality of answers: $\mathcal B(f_1)^*=\mathcal B(f_2)^*\Rightarrow f_1^*=f_2^*$ for $f_1,f_2\in\mathcal F$;
--   3. with $q_1(x,y)=x$ and $q_2(x,y)=\bar y$, for any $f_1,f_2\in\mathcal F$ and any $(x,y)\in[n]^{2k}$,
--   $$
--   \mathcal B(f_1)(x,y)\ne\mathcal B(f_2)(x,y)\ \Longrightarrow\ \exists j\in\{1,2\},\ f_1(q_j(x,y))\ne f_2(q_j(x,y)).
--   $$
--
--   These are the hypotheses of the adversary reduction lemma for $\iota=\mathcal B$ with $c=2$.
--
--   Differences from the source:
--   - encoding: a hard instance family for Tarski(n, k) in which every function has a unique fixed point → F : Set (Grid n k → Grid n k) with every member monotone and having a unique fixed point; reason: Definition 2.1: instances are monotone self-maps of [n]^k; "hard" adds no assumption beyond the stated witness
--   - encoding: [n]^{2k} → Grid n k × Grid n k with the product order; reason: order-isomorphic to the coordinatewise order on 2k coordinates (flattenBlocks n k 2)
--   - encoding: "B preserves equality of answers" → fixedPoint (B f₁) = fixedPoint (B f₂) → fixedPoint f₁ = fixedPoint f₂; reason: condition (2.15) for ι = B
--   - encoding: ∃ j ∈ {1, 2} with q₁(x, y) = x, q₂(x, y) = ȳ → f₁ x ≠ f₂ x ∨ f₁ ȳ ≠ f₂ ȳ; reason: two-element existential written out
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Lemma 3.9, PDF/printed p. 16, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Supplement_AntichainConstructor

namespace TarskiBootstrap.Dimensional.Supplement

/-- Lemma 3.9, PDF/printed p. 16: (1) every `B(f)`, `f ∈ F`, is monotone with a unique
fixed point, and the possible fixed points of `B(F)` form an antichain; (2) `B` preserves
equality of answers, (2.15); (3) with `q₁(x, y) = x`, `q₂(x, y) = ȳ`, a difference of
`B(f₁)` and `B(f₂)` at `(x, y)` forces `f₁(q_j(x, y)) ≠ f₂(q_j(x, y))` for some `j`. -/
theorem lemma_3_9 {n k : ℕ+} (F : Set (Grid n k → Grid n k))
    (hF : ∀ f : F, Monotone f.val ∧ ∃! x, f.val x = x) :
    ((∀ g : antichainFamily F, Monotone g.val ∧ ∃! p, g.val p = p) ∧
      IsAntichain (· ≤ ·) (possibleAnswers (antichainFamily F))) ∧
    (∀ f₁ f₂ : F,
      fixedPoint (antichainConstructor f₁.val) = fixedPoint (antichainConstructor f₂.val) →
        fixedPoint f₁.val = fixedPoint f₂.val) ∧
    (∀ f₁ f₂ : F, ∀ x y : Grid n k,
      antichainConstructor f₁.val (x, y) ≠ antichainConstructor f₂.val (x, y) →
        f₁.val x ≠ f₂.val x ∨ f₁.val (gridConj y) ≠ f₂.val (gridConj y)) := by sorry

end TarskiBootstrap.Dimensional.Supplement
