-- Prove2me | Theorems.Thm_QuasiStrictNE_lemma_4
-- name    : QuasiStrictNE.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:07:44.330528+00:00
-- url     : https://prove2.me/theorems/699f5ed7-ce45-43a9-a93c-fc75da6557c1
-- title:
--   Lemma 4 — condition 2 of Definition 6 is preserved by composition
-- statement:
--   For each instance $I$ let $f_I:D_1\to D_2$ and $g_I:D_2\to\mathbb R^{d_3}$ be composable continuous maps ($D_1\subseteq\mathbb R^{d_1}$, $D_2\subseteq\mathbb R^{d_2}$), with all dimensions $d_1,d_2,d_3$ bounded by a polynomial in $|I|$. If both $f$ and $g$ satisfy the second condition of Definition 6, then so does $g\circ f$.
--
--   Differences from the source:
--   - reading: a collection of hyperplanes dividing DI into polyhedral regions on each of which FI is affine, coefficients of encoding length polynomial in |I| uniformly → a finite set of rational hyperplanes (a pair with a = 0 is allowed and cuts nothing); on every closed sign cell intersected with the domain a rational affine formula; every coefficient of encoding length ≤ q(|I|) for one polynomial q; reason: the paper's own regions R_T are closed (p.16, 'including its boundary'); the number of hyperplanes is not bounded (p.16 uses one per subset T)
--   - generalization: instances I (strings) with size |I| → instances indexed by an arbitrary type ι with a size function, on arbitrary domain sets D₁, D₂; reason: taking ι the instance strings and size the length gives the source; the generality lets the lemma apply to the games of §4
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Lemma 4, p.15

import Mathlib
import Definitions.Def_QuasiStrictNE_PLCond2

namespace QuasiStrictNE

/-- **Lemma 4** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict Equilibria*,
arXiv:2611.06350, Lemma 4, p.15: "For each input instance I, let f and g be composable continuous
maps, with all dimensions polynomially bounded in |I|. If both maps satisfy the second condition of
Definition 6, then their composition satisfies the second condition as well").

Let instances `i` have size `size i`, and let `f i : D₁ i → D₂ i` and `g i : D₂ i → ℝ^{d₃ i}` be
continuous, with `D₁ i ⊆ ℝ^{d₁ i}`, `D₂ i ⊆ ℝ^{d₂ i}`, and the dimensions `d₁, d₂, d₃` bounded by a
polynomial in the size. If `f` and `g` satisfy condition 2 of Definition 6 (`PLCond2`) on `D₁` and
`D₂`, then `g ∘ f` satisfies it on `D₁`.

**Formalization Note** Instances are indexed by an arbitrary type with a size function, so the lemma
applies to the strings of Definition 6 and to the games of §4. -/
theorem lemma_4 {ι : Type} (size : ι → ℕ) (d₁ d₂ d₃ : ι → ℕ)
    (hdim : ∃ r : Polynomial ℕ, ∀ i, d₁ i ≤ r.eval (size i) ∧ d₂ i ≤ r.eval (size i) ∧
      d₃ i ≤ r.eval (size i))
    (D₁ : ∀ i, Set (Fin (d₁ i) → ℝ)) (D₂ : ∀ i, Set (Fin (d₂ i) → ℝ))
    (f : ∀ i, (Fin (d₁ i) → ℝ) → (Fin (d₂ i) → ℝ)) (g : ∀ i, (Fin (d₂ i) → ℝ) → (Fin (d₃ i) → ℝ))
    (hmaps : ∀ i, Set.MapsTo (f i) (D₁ i) (D₂ i))
    (hf : ∀ i, ContinuousOn (f i) (D₁ i)) (hg : ∀ i, ContinuousOn (g i) (D₂ i))
    (hf2 : PLCond2 size d₁ d₂ D₁ f) (hg2 : PLCond2 size d₂ d₃ D₂ g) :
    PLCond2 size d₁ d₃ D₁ (fun i => g i ∘ f i) := by sorry

end QuasiStrictNE
