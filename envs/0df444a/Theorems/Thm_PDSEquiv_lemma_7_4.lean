-- Prove2me | Theorems.Thm_PDSEquiv_lemma_7_4
-- name    : PDSEquiv.lemma_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:33.161886+00:00
-- url     : https://prove2.me/theorems/294e9c25-cc35-4037-93e4-53b270c33974
-- title:
--   Lemma 7.4 — concentration of $F(x)=\mathbb E_I[f_I(x_I)]$: $\Pr[|F(X)-\mathbb EF(X)|\ge t]\le2e^{-2t^2/\rho}$
-- statement:
--   Let $X=(X_1,\dots,X_M)$ consist of independent bits (with arbitrary biases). Let $I$ be a random subset of $[M]$, independent of $X$, and associate with each possible $I$ a function $f_I:\{0,1\}^I\to[0,1]$. Define $F(x)=\mathbb E_I[f_I(x_I)]$ and let $\rho>0$ satisfy $\Pr[i\in I]\le\rho$ for every $i\in[M]$. Then for every $t\ge0$,
--   $$\Pr\bigl[|F(X)-\mathbb EF(X)|\ge t\bigr]\le2\exp(-2t^2/\rho).$$
--
--   This read-$k$ type bound (Gavinsky–Lovett–Saks–Srinivasan; Hirahara–Shimizu) is the concentration tool for vertex scores.
--
--   Differences from the source:
--   - encoding: a random subset I of [M] and independent bits X → a mass function ν on subsets of Fin M and biases b_i ∈ [0, 1]; probabilities are finite sums; reason: the same finite laws
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Lemma 7.4, p.28 (PDF p.30)

import Mathlib

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Lemma 7.4, p.28 (PDF p.30).
Concentration for an average of functions of random subsets of independent bits.

**Formalization Note.** `b i` is the bias of the bit `X_i`, arbitrary in `[0, 1]`; `ν` is the law of `I`. -/
theorem lemma_7_4 (M : ℕ) (b : Fin M → ℝ) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (ν : Finset (Fin M) → ℝ) (hν : ∀ I, 0 ≤ ν I) (hν1 : ∑ I, ν I = 1)
    (f : ∀ I : Finset (Fin M), ({i // i ∈ I} → Bool) → ℝ) (hf : ∀ I x, 0 ≤ f I x ∧ f I x ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) (hρI : ∀ i, ∑ I ∈ Finset.univ.filter (fun I => i ∈ I), ν I ≤ ρ)
    (t : ℝ) (ht : 0 ≤ t) :
    let μ : (Fin M → Bool) → ℝ := fun x => ∏ i, (if x i then b i else 1 - b i)
    let F : (Fin M → Bool) → ℝ := fun x => ∑ I, ν I * f I (fun i => x i.1)
    let m : ℝ := ∑ x, μ x * F x
    ∑ x ∈ Finset.univ.filter (fun x => t ≤ |F x - m|), μ x ≤ 2 * Real.exp (-2 * t ^ 2 / ρ) := by sorry

end PDSEquiv
