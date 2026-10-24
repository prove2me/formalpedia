-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_theorem_1_5
-- name    : ProjSelfConcordant.ConicExt.theorem_1_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:24.614031+00:00
-- url     : https://prove2.me/theorems/dc73ce8a-ef3b-4bc2-bdd2-6df60f723bed
-- title:
--   Theorem 1.5, p. 3 — f is projectively self-concordant with γ = (ν − 2)/√(ν − 1) iff ν(−log t + f(t⁻¹x)) is self-concordant on the conic extension
-- statement:
--   Let $D\subset\mathbb R^n$ be an open convex set and $K=\{(t,x)\in\mathbb R^{n+1}\mid t>0,\ t^{-1}x\in D\}$ its conic extension. Let $f:D\to\mathbb R$ be a $C^3$ function, let $\nu\ge2$ be real, define $F:K\to\mathbb R$ by
--   $$F(t,x)=\nu\bigl(-\log t+f(t^{-1}x)\bigr),$$
--   and set $\gamma=(\nu-2)/\sqrt{\nu-1}$. Then the following are equivalent:
--
--   1. $f$ satisfies on $D$ conditions (1) and (3) of Definition 1.4 with parameter $\gamma$: for all $x\in D$ and $h$,
--   $$f''(x)[h,h]-(f'(x)[h])^2>0\ (h\ne0),\qquad \bigl|f'''(x)[h,h,h]-6f''(x)[h,h]f'(x)[h]+4(f'(x)[h])^3\bigr|\le2\gamma\bigl(f''(x)[h,h]-(f'(x)[h])^2\bigr)^{3/2};$$
--   2. $F$ satisfies on $K$ conditions (1) and (3) of Definition 1.1: for all $y\in K$ and $h$,
--   $$F''(y)[h,h]>0\ (h\ne0),\qquad |F'''(y)[h,h,h]|\le2\bigl(F''(y)[h,h]\bigr)^{3/2}.$$
--
--   The theorem says that projective self-concordance of a function on a convex set is exactly affine self-concordance of its logarithmically homogeneous extension to the cone over the set, with the sharp correspondence $\gamma=(\nu-2)/\sqrt{\nu-1}$ between the parameters.
--
--   **Formalization Note** $f$ and $F$ are total functions read only on the open sets $D$ and $K$; $\mathbb R^{n+1}$ is $\mathbb R\times\mathbb R^n$ with first coordinate $t$; derivatives are iterated Fréchet derivatives on the diagonal. The barrier conditions (2) and the parameter condition (4) are not part of the theorem, as on the page.
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 3, Theorem 1.5

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

namespace ProjSelfConcordant.ConicExt

/-- Theorem 1.5, p. 3: let `D ⊂ ℝⁿ` be open and convex, `K = {(t, x) | t > 0, t⁻¹x ∈ D}`, `f` a
`C³` function on `D`, `ν ≥ 2`, `F(t, x) = ν(−log t + f(t⁻¹x))` and `γ = (ν − 2)/√(ν − 1)`. Then
`f` satisfies conditions (1) and (3) of Definition 1.4 on `D` with parameter `γ` if and only if
`F` satisfies conditions (1) and (3) of Definition 1.1 on `K`. -/
theorem theorem_1_5 {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hDc : Convex ℝ D)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiffOn ℝ 3 f D) (ν : ℝ) (hν : 2 ≤ ν) :
    (ProjCond1 D f ∧ ProjCond3 ((ν - 2) / Real.sqrt (ν - 1)) D f) ↔
      (AffCond1 (conicExt D) (homExt ν f) ∧ AffCond3 (conicExt D) (homExt ν f)) := by sorry

end ProjSelfConcordant.ConicExt
