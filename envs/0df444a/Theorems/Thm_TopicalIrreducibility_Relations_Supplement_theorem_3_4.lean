-- Prove2me | Theorems.Thm_TopicalIrreducibility_Relations_Supplement_theorem_3_4
-- name    : TopicalIrreducibility.Relations.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:20:19.451197+00:00
-- url     : https://prove2.me/theorems/9ec67fcd-7e83-4412-a04e-839e22afdd72
-- title:
--   Theorem 3.4 — imperturbability, bounded slice spaces, and positive eigenvectors under diagonal scaling and uniform perturbation
-- statement:
--   Fix a finite dimension $n$ and let $f:\mathbb R^n_{\ge0}\to\mathbb R^n_{\ge0}$ be m-topical (continuous, order-preserving, homogeneous, with $f(\mathbb R^n_{>0})\subseteq\mathbb R^n_{>0}$). The following four conditions are equivalent:
--
--   1. $f$ is imperturbable;
--   2. for all real $\alpha,\beta>0$ the slice space $S_\alpha^\beta(f)=\{x\in\mathbb R^n_{>0}:\alpha x\le f(x)\le\beta x\}$ is bounded in Hilbert's projective metric $d_H$;
--   3. for every diagonal matrix $D$ with positive diagonal entries, $D\circ f$ has an eigenvector in $\mathbb R^n_{>0}$;
--   4. every m-topical map $g$ on $\mathbb R^n_{\ge0}$ that is a Hilbert metric uniform perturbation of $f$, i.e.
--   $$
--   \sup_{x\in\mathbb R^n_{>0}} d_H\bigl(f(x),g(x)\bigr)<\infty,
--   $$
--   has an eigenvector in $\mathbb R^n_{>0}$.
--
--   The theorem (due to Akian, Gaubert and Hochart) characterizes the combinatorial condition of imperturbability as exactly the robust existence of entrywise positive eigenvectors, and it is the tool used to prove Theorem 3.5.
--
--   **Formalization Note** The four conditions are a `List.TFAE`. Each slice space has its own finite bound, which may depend on $\alpha,\beta$; the perturbation bound may depend on $g$ but not on $x$; the eigenvector and eigenvalue may depend on $D$ and $g$. Eigenvalues are positive reals; for m-topical maps an eigenvalue at an interior vector is automatically positive.
--
--   Differences from the source:
--   - encoding: diagonal matrices D with positive diagonal entries acting on f(x) → vectors d with positive entries and (D∘f)(x)_i = d_i f(x)_i; reason: same maps
--   - encoding: eigenvector in R^n_{>0} with real eigenvalue → interior u and λ ∈ ℝ≥0 with λ > 0; reason: for n > 0 an interior u is nonzero and the maps D∘f and g are m-topical, so the eigenvalue f(u)_i/u_i is positive; same instances
--   - encoding: d_H defined on R^n_{>0} for n ≥ 1 → published hilbertDist on real coordinates, value 0 on Fin 0, and the empty vector an interior eigenvector; reason: the case n = 0 is an extension in which all four conditions hold; all positive-dimensional instances are the source's
-- source:
--   Brian Lins, Irreducibility for Topical Maps, STOC 2027 submission #201 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/201.pdf, Theorem 3.4, p. 7 (PDF p. 7); definitions pp. 2–3, 6–7

import Mathlib
import Definitions.Def_TopicalIrreducibility_Relations_MTopical
import Definitions.Def_TopicalIrreducibility_Relations_Supplement_Conditions

open scoped NNReal

namespace TopicalIrreducibility.Relations.Supplement

open TopicalIrreducibility.Relations

/-- Theorem 3.4 (p. 7). For an m-topical `f` on `ℝⁿ_{≥0}` the following are equivalent:
(1) `f` is imperturbable; (2) every slice space `S_α^β(f)`, `α, β > 0`, is bounded in Hilbert's
projective metric; (3) `D ∘ f` has an eigenvector in `ℝⁿ_{>0}` for every diagonal `D` with
positive diagonal entries; (4) every m-topical Hilbert metric uniform perturbation `g` of `f`
has an eigenvector in `ℝⁿ_{>0}`. -/
theorem theorem_3_4 {n : ℕ} (f : StdCone n → StdCone n) (hf : IsMTopical f) :
    List.TFAE
      [ Imperturbable f,
        ∀ α β : ℝ≥0, 0 < α → 0 < β → HilbertBounded (sliceSpace f α β),
        ∀ d : Fin n → ℝ≥0, (∀ i, 0 < d i) → HasInteriorEigenvector (diagComp d f),
        ∀ g : StdCone n → StdCone n, IsMTopical g → IsHilbertUniformPerturbation f g →
          HasInteriorEigenvector g ] := by sorry

end TopicalIrreducibility.Relations.Supplement
