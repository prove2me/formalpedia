-- Prove2me | Theorems.Thm_SteinerAPX_kirszbraun
-- name    : SteinerAPX.kirszbraun
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:33:16.657561+00:00
-- url     : https://prove2.me/theorems/34b52b49-1c06-4233-9a9e-e3d05e28c624
-- title:
--   Kirszbraun's extension theorem for maps $A\subseteq\mathbb R^D\to\mathbb R^{D'}$
-- statement:
--   Let $A\subseteq\mathbb R^D$ be any set and $f:A\to\mathbb R^{D'}$ a $\lambda$-Lipschitz map, i.e. $\|f(x)-f(y)\|\le\lambda\|x-y\|$ for all $x,y\in A$. Then $f$ extends to a $\lambda$-Lipschitz map $F:\mathbb R^D\to\mathbb R^{D'}$:
--   $$
--   F(a)=f(a)\ \ (a\in A),\qquad \|F(x)-F(y)\|\le\lambda\|x-y\|\ \ (x,y\in\mathbb R^D).
--   $$
--
--   The extension carries the Steiner points of a network along with the terminals, which is how optimal Steiner lengths are compared under a change of dimension (Lemma 17).
--
--   **Formalization Note** $f$ is given as a map on all of $\mathbb R^D$ that is Lipschitz on $A$; only its values on $A$ matter. $\lambda$ is a nonnegative real. The target has any finite dimension and the constant is preserved, unlike McShane's real-valued extension.
--
--   Differences from the source:
--   - encoding: f : A → ℝᴰ′ and λ-Lipschitz with λ real → f : ℝᴰ → ℝᴰ′ Lipschitz on A with constant λ ∈ ℝ≥0; reason: any map on A extends arbitrarily to ℝᴰ; a Lipschitz constant is nonnegative
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §5.2, p.22 (PDF p.24) (Kirszbraun [31])

import Mathlib

namespace SteinerAPX

/-- **Kirszbraun's extension theorem.** S. Bartlmae, *Inapproximability of Euclidean Steiner
Tree*, STOC 2027 submission (manuscript sha256 6f78a9ea…), §5.2, p.22 (PDF p.24): "For A ⊆ RD, a
map f : A → RD′ is λ-Lipschitz if ∥f(x) − f(y)∥ ≤ λ∥x − y∥ for all x, y ∈ A. By Kirszbraun's
theorem, f extends to a λ-Lipschitz map F : RD → RD′, that is, F(a) = f(a) for all a ∈ A,
∥F(x) − F(y)∥ ≤ λ∥x − y∥ for all x, y ∈ RD."

For finite-dimensional Euclidean spaces `ℝᴰ`, `ℝᴰ'`, every set `A ⊆ ℝᴰ` and every map `f` that is
`λ`-Lipschitz on `A`, there is a `λ`-Lipschitz map `F : ℝᴰ → ℝᴰ'` agreeing with `f` on `A`.

**Formalization Note** `f` is a map on all of `ℝᴰ` that is Lipschitz on `A` (`LipschitzOnWith`);
only its values on `A` matter. `λ` is a nonnegative real (`ℝ≥0`). `A` is arbitrary, not only
finite; the target is multi-dimensional with the same constant (not McShane's real-valued
extension). -/
theorem kirszbraun {ι ι' : Type} [Fintype ι] [Fintype ι'] (A : Set (EuclideanSpace ℝ ι))
    (f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι') (K : NNReal) (hf : LipschitzOnWith K f A) :
    ∃ F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι', LipschitzWith K F ∧ Set.EqOn F f A := by sorry

end SteinerAPX
