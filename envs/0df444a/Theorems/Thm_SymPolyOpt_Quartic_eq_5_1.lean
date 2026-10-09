-- Prove2me | Theorems.Thm_SymPolyOpt_Quartic_eq_5_1
-- name    : SymPolyOpt.Quartic.eq_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:38.065515+00:00
-- url     : https://prove2.me/theorems/fb7317a4-ae04-4b9b-b129-f72f7271f3d0
-- title:
--   (5.1), p. 22 — inf over K of f equals the minimum over r-partitions ω of inf over K^ω of f^ω
-- statement:
--   Let $f, g_1, \dots, g_m \in \mathbb R[X_1, \dots, X_n]$ be symmetric, $K = \{x \in \mathbb R^n : g_j(x) \ge 0,\ j = 1, \dots, m\}$, and $r := \max\{2, \lfloor (\deg f)/2 \rfloor, \deg g_1, \dots, \deg g_m\}$, and assume $r \le n$. Let $\Omega$ be the set of $r$-partitions of $n$, and for $\omega \in \Omega$ let $f^\omega, g_j^\omega \in \mathbb R[T_1, \dots, T_r]$ be the restrictions and $K^\omega := \{t \in \mathbb R^r : g_1^\omega(t) \ge 0, \dots, g_m^\omega(t) \ge 0\}$. Then
--   $$\inf_{x \in K} f(x) = \min_{\omega \in \Omega} \inf_{t \in K^\omega} f^\omega(t).$$
--
--   This turns one optimization problem in $n$ variables into finitely many problems in $r$ variables.
--
--   **Formalization Note** All infima are in the extended reals, and the minimum over the finite set $\Omega$ is an infimum. The hypothesis $r \le n$ is not printed on the page: when $r > n$ there is no $r$-partition of $n$, the right-hand side is $+\infty$, and the identity fails for every nonempty $K$. Theorem 5.5 uses the case $r = 2 \le n$.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 22, display (5.1)

import Mathlib
import Definitions.Def_SymPolyOpt_Quartic_Setting

namespace SymPolyOpt.Quartic

open MvPolynomial

/-- Display (5.1): for symmetric `f, g_1, …, g_m`, `r = max{2, ⌊deg f / 2⌋, deg g_1, …, deg g_m}`
and `r ≤ n`, `inf_{x ∈ K} f(x) = min_{ω ∈ Ω} inf_{t ∈ K^ω} f^ω(t)`, where `Ω` is the set of
`r`-partitions of `n` (as block maps) and `K^ω = {t ∈ ℝ^r : g^ω_j(t) ≥ 0}`. Infima in `EReal`. -/
theorem eq_5_1 {n m : ℕ} (f : MvPolynomial (Fin n) ℝ)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (hf : f.IsSymmetric) (hg : ∀ j, (g j).IsSymmetric) (hr : degreeR f g ≤ n) :
    ⨅ x ∈ SymPolyOpt.Putinar.feasK g, ((eval x f : ℝ) : EReal) =
      ⨅ (b : Fin n → Fin (degreeR f g)) (_ : IsBlockMap b),
        ⨅ t ∈ SymPolyOpt.Putinar.feasK (fun j => restrict b (g j)), ((eval t (restrict b f) : ℝ) : EReal) := by sorry

end SymPolyOpt.Quartic
