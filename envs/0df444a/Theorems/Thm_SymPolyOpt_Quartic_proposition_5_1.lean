-- Prove2me | Theorems.Thm_SymPolyOpt_Quartic_proposition_5_1
-- name    : SymPolyOpt.Quartic.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:41.294548+00:00
-- url     : https://prove2.me/theorems/a2dc4a9b-349a-4e8d-ace3-f26a99e3264c
-- title:
--   Proposition 5.1, p. 21 — degree principle: inf over K of f equals inf over K ∩ A_r
-- statement:
--   Let $f, g_1, \dots, g_m \in \mathbb R[X_1, \dots, X_n]$ be symmetric polynomials (invariant under every permutation of the variables), let $K = \{x \in \mathbb R^n : g_1(x) \ge 0, \dots, g_m(x) \ge 0\}$, and set
--   $r := \max\{2, \lfloor (\deg f)/2 \rfloor, \deg g_1, \dots, \deg g_m\}$. Let $A_r$ be the set of points of $\mathbb R^n$ with at most $r$ distinct components. Then
--   $$\inf_{x \in K} f(x) = \inf_{x \in K \cap A_r} f(x).$$
--
--   This is the degree principle of Timofte, in the refined form of Riener: a symmetric problem can be minimized over points with few distinct coordinates. It is quoted in the paper from [33, Theorem 4.5] and is the input of the reduction (5.1) and of the "if" direction of Theorem 5.5.
--
--   **Formalization Note** Both infima are taken in the extended reals $\overline{\mathbb R}$, so they are $+\infty$ when the set is empty and may be $-\infty$; no arithmetic on extended reals occurs. Symmetry is Mathlib's `MvPolynomial.IsSymmetric`.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 21, Proposition 5.1 (citing [33, Theorem 4.5])

import Mathlib
import Definitions.Def_SymPolyOpt_Quartic_Setting

namespace SymPolyOpt.Quartic

open MvPolynomial

/-- Proposition 5.1 (degree principle, [33, Theorem 4.5]): for symmetric `f, g_1, …, g_m` and
`K = {g_j ≥ 0}`, with `r = max{2, ⌊deg f / 2⌋, deg g_1, …, deg g_m}`,
`inf_{x ∈ K} f(x) = inf_{x ∈ K ∩ A_r} f(x)`. Infima are taken in `EReal`. -/
theorem proposition_5_1 {n m : ℕ} (f : MvPolynomial (Fin n) ℝ)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (hf : f.IsSymmetric) (hg : ∀ j, (g j).IsSymmetric) :
    ⨅ x ∈ SymPolyOpt.Putinar.feasK g, ((eval x f : ℝ) : EReal) =
      ⨅ x ∈ SymPolyOpt.Putinar.feasK g ∩ A n (degreeR f g), ((eval x f : ℝ) : EReal) := by sorry

end SymPolyOpt.Quartic
