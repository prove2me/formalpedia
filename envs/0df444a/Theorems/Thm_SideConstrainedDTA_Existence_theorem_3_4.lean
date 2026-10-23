-- Prove2me | Theorems.Thm_SideConstrainedDTA_Existence_theorem_3_4
-- name    : SideConstrainedDTA.Existence.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:43.956254+00:00
-- url     : https://prove2.me/theorems/526e0865-8b1c-4401-8afe-f4faf0941789
-- title:
--   Theorem 3.4, p. 12 — Lions: a VI on a nonempty closed convex bounded C ⊆ L²([a,b])^d with a sequentially weak-strong continuous map has a solution
-- statement:
--   Let $a,b\in\mathbb R$, $d\in\mathbb N$, and let $H=L^2([a,b])^d$ with the scalar product $\langle f,g\rangle=\sum_{k=1}^d\int_a^b f_k g_k$. Let $C\subseteq H$ be non-empty, closed, convex and bounded, and let $\mathcal A:C\to H$ be **sequentially weak-strong continuous**: whenever $x^n\in C$ converges weakly to $x^0\in C$ (that is, $\langle x^n,g\rangle\to\langle x^0,g\rangle$ for every $g\in H$), then $\mathcal A(x^n)\to\mathcal A(x^0)$ in norm. Then there is $h^*\in C$ with
--   $$\langle\mathcal A(h^*),h-h^*\rangle\ge0\qquad\text{for all }h\in C.$$
--
--   This is Lions' existence theorem for variational inequalities, in the form the paper restates; it is the engine behind the existence of unconstrained dynamic equilibria (Theorem 3.5).
--
--   **Formalization Note.** $H$ is `PiLp 2` of $d$ copies of `Lp ℝ 2` on $[a,b]$, whose inner product is the paper's $\langle\cdot,\cdot\rangle$. The map is a total function on $H$; only its values on $C$ enter the hypothesis and the conclusion. Weak convergence is tested against every element of $H$ (Riesz representation).
-- source:
--   Graf, Harks, Side-Constrained Dynamic Traffic Equilibria, arXiv:2211.03194v3, p. 12, Theorem 3.4 (from Lions 1969, Chapitre 2, Théorème 8.1)

import Mathlib

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence

/-- Theorem 3.4 (Lions), p. 12: on `H = L²([a, b])^d`, a sequentially weak-strong continuous map
`A` on a non-empty, closed, convex, bounded set `C` admits a solution of the variational
inequality `⟨A(h*), h − h*⟩ ≥ 0` for all `h ∈ C`. -/
theorem theorem_3_4 (a b : ℝ) (d : ℕ)
    (C : Set (PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Icc a b)))))
    (A : PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Icc a b))) →
      PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Icc a b))))
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C)
    (hbdd : Bornology.IsBounded C)
    (hA : ∀ (x : ℕ → PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Icc a b))))
      (x₀ : PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Icc a b)))),
      (∀ n, x n ∈ C) → x₀ ∈ C →
      (∀ g, Tendsto (fun n => inner ℝ (x n) g) atTop (𝓝 (inner ℝ x₀ g))) →
      Tendsto (fun n => A (x n)) atTop (𝓝 (A x₀))) :
    ∃ h ∈ C, ∀ y ∈ C, 0 ≤ inner ℝ (A h) (y - h) := by sorry

end SideConstrainedDTA.Existence
