-- Prove2me | Theorems.Thm_Transcendence_partials_eq_iteratedFDeriv
-- name    : Transcendence.partials_eq_iteratedFDeriv
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:18:47.76386+00:00
-- url     : https://prove2.me/theorems/a03f7908-0087-4475-9655-737ef73c454e
-- title:
--   Iterated partial derivatives along coordinate slices are the values of iteratedFDeriv on coordinate vectors
-- statement:
--   Let $\mathbb{K}$ be a nontrivially normed field, $\iota$ a finite set, $F$ a normed space over $\mathbb{K}$, and $g : \mathbb{K}^\iota \to F$ a function of class $C^k$. For a function $h$ on $\mathbb{K}^\iota$ and $i \in \iota$, let $\partial_ih(z)$ be the derivative at $w = z_i$ of the slice $w \mapsto h(z[i := w])$, where $z[i := w]$ is $z$ with its coordinate $z_i$ replaced by $w$. Then for every list of directions $L : \{0, \dots, k-1\} \to \iota$ and every $z \in \mathbb{K}^\iota$,
--
--   $$\partial_{L(0)}\,\partial_{L(1)}\cdots\partial_{L(k-1)}\,g\,(z) = D^kg(z)\,(e_{L(0)}, \dots, e_{L(k-1)}),$$
--
--   where the partial derivative in the direction $L(k-1)$ is taken first, $D^kg$ is the $k$-th Fréchet derivative (`iteratedFDeriv`) and $e_\nu$ are the coordinate vectors.
--
--   It connects the slice derivatives, to which one-variable complex analysis applies, with the derivatives in which the other nodes are stated; `Transcendence.polydisc_cauchy` and `Transcendence.coord_hermite_step` use it.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: a standard fact of differential calculus, stated in Mathlib's terms. The contribution of this node is the formal proof.
-- source:
--   Standard. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **Coordinate partial derivatives are values of `iteratedFDeriv`.** Let `g` be a `C^k` function of the
variables `z_ν` (`ν ∈ ι`) over a nontrivially normed field. The partial derivative of `g` in the variable `z_i`
at `z` is the derivative at `w = z_i` of the slice `w ↦ g(z[i := w])`, where `z[i := w]` is `z` with its
coordinate `z_i` replaced by `w`. Taking such partial derivatives in the variables `L (k-1), …, L 1, L 0`, in
this order, gives at `z` the `k`-th derivative of `g` at `z` applied to the coordinate vectors
`e_{L 0}, …, e_{L (k-1)}`. -/
theorem partials_eq_iteratedFDeriv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {k : ℕ} (L : Fin k → ι) {g : (ι → 𝕜) → F} (hg : ContDiff 𝕜 k g) (z : ι → 𝕜) :
    (List.ofFn L).foldr (fun i h y => deriv (fun w => h (Function.update y i w)) (y i)) g z =
      iteratedFDeriv 𝕜 k g z (fun l => Pi.single (L l) 1) := by
  sorry

end Transcendence
