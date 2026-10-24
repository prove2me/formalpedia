-- Prove2me | Theorems.Thm_TalagrandConc1995_thm4_1_1_convex_hull_faithful
-- name    : TalagrandConc1995.thm4_1_1_convex_hull_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T03:19:01.414183+00:00
-- url     : https://prove2.me/theorems/473e3c4d-d4e9-40ba-80b8-e2e4e35a3357
-- title:
--   Theorem 4.1.1 — Talagrand's convex hull inequality $\int e^{f_c^2/4}\,dP\le 1/P(A)$
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and $P=\mu^{\otimes N}$ on $\Omega^N$. For $A\subseteq\Omega^N$ and $x\in\Omega^N$ let
--   $U_A(x)=\{s\in\{0,1\}^N:\ \exists y\in A,\ s_i=0\Rightarrow x_i=y_i\}$, let $V_A(x)$ be the convex hull of $U_A(x)$ in $\mathbb R^N$, let $f_c(A,x)$ be the Euclidean distance from $0$ to $V_A(x)$, and let $A_t^c=\{x:\ f_c(A,x)\le t\}$. Then for every measurable $A$
--
--   $$\int_{\Omega^N}\exp\Big(\tfrac14 f_c^2(A,x)\Big)\,dP(x)\le\frac1{P(A)},\qquad P(A_t^c)\ge 1-\frac1{P(A)}e^{-t^2/4}\quad(t\ge0).$$
--
--   This is Theorem 4.1.1 of Talagrand (1995), the convex hull inequality on which Chapters 6–9 and 13 of the paper rely. It is the case $\alpha=1$ of Theorem 4.2.4 (the goal of the Convex Hull Distance mission) combined with Lemma 4.2.2.
--
--   **Formalization Note** $f_c$ takes values in $[0,\infty]$ and equals $+\infty$ only for $A=\emptyset$; there the real conversion gives $0$, the left side is $1$ and $1/P(A)=+\infty$, so the statement stays true and contentless, as in the paper. The measurability of $A$ and of $f_c(A,\cdot)$ encodes the paper's convention of treating all sets and functions as measurable (p. 81); the second part is stated for $t\ge0$, the range in which $A_t^c$ is an enlargement.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), doi:10.1007/BF02699376, p. 123, Theorem 4.1.1, Eqs. (4.1.2)–(4.1.3)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

open MeasureTheory
open scoped ENNReal

theorem TalagrandConc1995.thm4_1_1_convex_hull_faithful {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}
    (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hfc : Measurable (fun x => TalagrandConc.ConvexHull.fc A x)) :
    (∫⁻ x, ENNReal.ofReal (Real.exp ((TalagrandConc.ConvexHull.fc A x).toReal ^ 2 / 4))
        ∂(Measure.pi fun _ : Fin N => μ)) ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ ∧
      ∀ t : ℝ, 0 ≤ t →
        1 - ((Measure.pi fun _ : Fin N => μ) A)⁻¹ * ENNReal.ofReal (Real.exp (-(t ^ 2 / 4))) ≤
          (Measure.pi fun _ : Fin N => μ) (TalagrandConc.ConvexHull.enlarge A t) := by sorry
