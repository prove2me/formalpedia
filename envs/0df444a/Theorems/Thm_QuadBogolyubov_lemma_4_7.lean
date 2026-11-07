-- Prove2me | Theorems.Thm_QuadBogolyubov_lemma_4_7
-- name    : QuadBogolyubov.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:04:58.590037+00:00
-- url     : https://prove2.me/theorems/566792a8-7edf-486c-b903-d48baa7c8293
-- title:
--   Lemma 4.7 — density increment
-- statement:
--   Let $A,W\subseteq\mathbb F_2^n$ with $W\ne\emptyset$, let $q:\mathbb F_2^n\to\mathbb F_2$ and let $\delta,\gamma$ be real numbers with
--   $$|A\cap W|\ge\delta|W|\quad\text{and}\quad\Big|\mathbb E_{x\in W}(\mathbf 1_A(x)-\delta)(-1)^{q(x)}\Big|\ge\gamma.$$
--   Then there is $b\in\mathbb F_2$ such that $W_b=\{x\in W:q(x)=b\}$ is non-empty and
--   $$\frac{|A\cap W_b|}{|W_b|}\ge\delta+\frac{\gamma}{4}\cdot\frac{|W|}{|W_b|}.$$
--   This turns correlation with a phase into a density increment on a level set.
--
--   Differences from the source:
--   - generalization: q left unspecified on the page (a quadratic function where the lemma is applied, p.14) → q : 𝔽₂ⁿ → ZMod 2 arbitrary; reason: the printed proof uses nothing about q; a quadratic q is a special case
--   - encoding: E_{x∈W} → the hypothesis `W.Nonempty`; reason: an average over W needs W ≠ ∅; for W = ∅ the printed expression is undefined
--   - reading: "the set W_b … satisfies |A ∩ W_b|/|W_b| ≥ …" → also `W_b.Nonempty`; reason: the ratio is meant for W_b ≠ ∅; the proof averages over the level sets with non-negative sum
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
--   - encoding: (−1)^{q(x)} with exponent in F₂ → `(-1 : ℝ) ^ (q x).val`; reason: the exponent is the value in {0, 1}; casting to ℝ would break 1 + 1 = 0
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Lemma 4.7, p.12

import Mathlib
import Definitions.Def_QuadBogolyubov_gowersU3

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Lemma 4.7 (Density increment).** Let `A, W ⊆ 𝔽₂ⁿ` with `W ≠ ∅`, `q : 𝔽₂ⁿ → 𝔽₂`, and real
`δ, γ` with `|A ∩ W| ≥ δ|W|` and `|𝔼_{x∈W}(1_A(x) − δ)(−1)^{q(x)}| ≥ γ`. Then there is `b ∈ 𝔽₂`
such that `W_b := {x ∈ W : q(x) = b}` is non-empty and
`|A ∩ W_b| / |W_b| ≥ δ + (γ/4) · |W| / |W_b|`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Lemma 4.7, p.12: "Suppose A, W ⊆ F₂ⁿ are sets satisfying |A ∩ W| ≥ δ|W| and
|E_{x∈W}(1A(x) − δ)(−1)^{q(x)}| ≥ γ. Then, there exists b ∈ F2 such that the set
Wb := {x ∈ W : q(x) = b} satisfies |A ∩ Wb| / |Wb| ≥ δ + (γ/4) · |W|/|Wb|."

**Formalization Note.** `W ≠ ∅` is assumed because `𝔼_{x∈W}` is an average over `W`. The
conclusion adds `W_b ≠ ∅`, since the ratio `|A ∩ W_b|/|W_b|` is meant for a non-empty `W_b`.
`q` is an arbitrary function (the lemma does not use that it is quadratic). -/
theorem lemma_4_7 {n : ℕ} (A W : Finset (Fin n → ZMod 2)) (q : (Fin n → ZMod 2) → ZMod 2)
    (δ γ : ℝ) (hW : W.Nonempty)
    (hdens : δ * (W.card : ℝ) ≤ ((A ∩ W).card : ℝ))
    (hcorr : γ ≤ |𝔼 x ∈ W, ((ind A x : ℝ) - δ) * (-1 : ℝ) ^ (q x).val|) :
    ∃ b : ZMod 2, (W.filter (fun x => q x = b)).Nonempty ∧
      δ + (γ / 4) * ((W.card : ℝ) / ((W.filter (fun x => q x = b)).card : ℝ)) ≤
        ((A ∩ W.filter (fun x => q x = b)).card : ℝ) /
          ((W.filter (fun x => q x = b)).card : ℝ) := by sorry

end QuadBogolyubov
