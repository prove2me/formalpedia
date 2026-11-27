-- Prove2me | Theorems.Thm_PseudoRiemannian_all_plus_positive_definite
-- name    : PseudoRiemannian.all_plus_positive_definite
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T02:30:24.606233+00:00
-- url     : https://prove2.me/theorems/3834842d-aeb5-52d1-8d74-7f0029f14874
-- title:
--   The Riemannian special case: all-plus signature is positive definite
-- statement:
--   **The Riemannian special case — all-plus signature is positive definite.**
--
--   The source's definition "is a generalization of a Riemannian manifold in which the requirement of positive-definiteness is relaxed". This rung shows the Riemannian world is exactly the all-plus corner of the pseudo-Riemannian one: let `B` be invertible and
--
--   $$B^{T}\, g(x)\, B \;=\; 1 \quad (\text{the identity matrix — signature vector constantly } +1).$$
--
--   **Conclusion:** for every vector `u`, the pairing at `x` is positive semidefinite and its null locus is trivial:
--
--   $$0 \;\le\; \mathrm{pair}(g, x, u, u) \qquad \text{and} \qquad \mathrm{pair}(g, x, u, u) = 0 \;\to\; u = 0.$$
--
--   In words: $g_x$ is a positive definite bilinear form — an inner product — so `Spc n` with such a metric is Riemannian in the classical sense.
--
--   **Formalization note.** From $B^{T} g B = 1$ with $B$ invertible, $g = (B^{-1})^{T} B^{-1}$, so
--
--   $$\mathrm{pair}(u, u) = u^{T} g u = (B^{-1} u)^{T} (B^{-1} u) \;=\; \|B^{-1} u\|^2 \;\ge\; 0,$$
--
--   and equality forces $B^{-1} u = 0$, i.e. $u = 0$ (`hB` gives $B^{-1}$ as a unit; the matrix manipulations are congruence algebra with `mul_left_inverse`/`mul_right_inverse`). Neither smoothness nor a curve is involved: pointwise linear algebra.
-- source:
--   Wikipedia, Pseudo-Riemannian manifold, https://en.wikipedia.org/wiki/Pseudo-Riemannian_manifold (source of the quoted statements, reproduced verbatim in the definition file) ('This is a generalization of a Riemannian manifold in which the requirement of positive-definiteness is relaxed')

import Mathlib
import Definitions.Def_PseudoRiemannian

namespace PseudoRiemannian

open Matrix
open scoped ContDiff

/-- Milestone: the Riemannian special case.  The source's definition "is a
generalization of a Riemannian manifold in which the requirement of
positive-definiteness is relaxed" — conversely, a metric congruent to the
all-plus identity (`Bᵀ (g x) B = 1`, signature vector constantly `+1`) has a
positive definite pairing at `x`:

`pair g x u u ≥ 0` for all `u`, and `pair g x u u = 0 → u = 0`,

i.e. `R^n` with such a metric is Riemannian in the classical sense. -/
theorem all_plus_positive_definite {n : ℕ} {g : Spc n → Matrix (Fin n) (Fin n) ℝ}
    {x : Spc n} {B : Matrix (Fin n) (Fin n) ℝ} (hB : IsUnit B.det)
    (hcong : Bᵀ * g x * B = (1 : Matrix (Fin n) (Fin n) ℝ)) (u : Spc n) :
    0 ≤ pair g x u u ∧ (pair g x u u = 0 → u = 0) := by
  sorry

end PseudoRiemannian
