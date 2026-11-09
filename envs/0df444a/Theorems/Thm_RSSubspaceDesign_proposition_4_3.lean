-- Prove2me | Theorems.Thm_RSSubspaceDesign_proposition_4_3
-- name    : RSSubspaceDesign.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:28:36.007766+00:00
-- url     : https://prove2.me/theorems/c02ff964-9e15-41f7-acd1-d2d5f8010d74
-- title:
--   Proposition 4.3 — rational ranks of the coordinate kernels: $\sum_i t_i\le t(k-1)+bt\log_2 t$
-- statement:
--   Let $K\subseteq F$ be finite fields, let $1\le k\le n$, and let $A=(\alpha_1,\dots,\alpha_n)$ be $(n,g,b,r)_{F,K}$-effective. Let $\{0\}\ne W\subseteq F[X]_{<k}$ be a $K$-subspace with $\dim_KW=e\le r$, and let $t=\dim_{K(X)}\operatorname{span}_{K(X)}(W)$ (so $t\le e$). Set
--   $$W_i=\{f\in W:f(\alpha_i)=0\},\qquad t_i=\dim_{K(X)}\operatorname{span}_{K(X)}(W_i).$$
--   Then
--   $$\sum_{i=1}^n t_i\;\le\;t(k-1)+b\,t\log_2t.$$
--
--   This is the rank form of the subspace-design bound; Theorem 4.4 converts it into the dimension bound of Theorem 4.2.
--
--   Differences from the source:
--   - encoding: dim_{K(X)} span_{K(X)}(W) = t ≤ e; t_i → t := ratRank K W and tᵢ := ratRank K Wᵢ (dimension over RatFunc K of the span in RatFunc F); t ≤ e is not assumed; reason: t ≤ e holds for every W (a K-basis of W spans its K(X)-span), so it restricts nothing
--   - encoding: W ⊆ F[X]_{<k}, dim_K W = e ≤ r → W : Submodule K F[X] with W ≤ degreeLT F k (as a K-space) and finrank K W ≤ r; reason: W is finite-dimensional over K, so finrank is its dimension
--   - encoding: K ⊆ F finite fields; k − 1; log₂ → an algebra K → F with F finite; (k : ℝ) − 1; Real.logb 2; reason: K embeds in F, so it is finite; Lean conventions; same values
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Proposition 4.3, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_RSSubspaceDesign_IsEffective
import Definitions.Def_RSSubspaceDesign_ratRank

open Polynomial

namespace RSSubspaceDesign

/-- **Proposition 4.3 (Rational ranks of the coordinate kernels).** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Proposition 4.3, p.19.

Let `K ⊆ F` be finite fields, `1 ≤ k ≤ n`, and `A = (α₁, …, αₙ)` be `(n, g, b, r)_{F,K}`-effective.
Let `{0} ≠ W ⊆ F[X]_{<k}` be a `K`-subspace with `dim_K W = e ≤ r` and
`dim_{K(X)} span_{K(X)}(W) = t`. Set `Wᵢ = {f ∈ W : f(αᵢ) = 0}` and
`tᵢ = dim_{K(X)} span_{K(X)}(Wᵢ)`. Then `∑ᵢ tᵢ ≤ t(k − 1) + b t log₂ t`.

**Formalization Note.** `t` and `tᵢ` are `ratRank K` (the `K(X)`-dimension of the span inside
`F(X)`). The paper's "`t ≤ e`" is a consequence, not a hypothesis, and is not assumed. `K` is finite
because it embeds in the finite field `F`. `F[X]_{<k}` is `degreeLT F k` viewed as a `K`-space.
`k − 1` is computed in `ℝ`. -/
theorem proposition_4_3 {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F]
    {n g b r k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (α : Fin n → F) (hα : IsEffective K n g b r α)
    (W : Submodule K F[X]) (hW0 : W ≠ ⊥) (hWk : W ≤ (degreeLT F k).restrictScalars K)
    (hWr : Module.finrank K W ≤ r) :
    (∑ i : Fin n, (ratRank K {f : F[X] | f ∈ W ∧ f.eval (α i) = 0} : ℝ)) ≤
      (ratRank K (W : Set F[X]) : ℝ) * ((k : ℝ) - 1) +
        (b : ℝ) * ratRank K (W : Set F[X]) * Real.logb 2 (ratRank K (W : Set F[X])) := by sorry

end RSSubspaceDesign
