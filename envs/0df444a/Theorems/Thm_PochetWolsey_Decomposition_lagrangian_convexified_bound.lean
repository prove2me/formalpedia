-- Prove2me | Theorems.Thm_PochetWolsey_Decomposition_lagrangian_convexified_bound
-- name    : PochetWolsey.Decomposition.lagrangian_convexified_bound
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:47.4947+00:00
-- url     : https://prove2.me/theorems/9b83786a-b6f8-4af1-9cd8-6d52cca51215
-- title:
--   Theorem 6.5 — Lagrangian and convexified decomposition bounds
-- statement:
--   Let $A,b$ be rational data defining $Y=\{x\in\mathbb Z^n:x\ge0,Ax\ge b\}$. Let $D,d,c$ be real and set $P_Z=\{x\ge0:Dx\ge d\}$ and $H=\operatorname{conv}(Y)\cap P_Z$. Assume $H$ is nonempty and $cx$ is bounded below on $H$. Let $R=\{x\ge0:Bx\ge e\}=\operatorname{conv}(Y)$ be a tight finite formulation with real data. Define
--   $$
--   L(\pi)=\inf_{y\in Y}\bigl(cy+\pi(d-Dy)\bigr),\qquad w=\inf_{x\in H}cx.
--   $$
--   The full column master ranges over all finite convex combinations of points of $Y$ plus nonnegative combinations of nonzero recession directions $u\ge0$, $Au\ge0$, subject to $P_Z$. Let $w_{\rm col}$ be its infimum. Under the preceding section's literal maximum convention, put $z_{LP}=\sup_{x\in R\cap P_Z}cx$. The assertion is
--   $$
--   w=\max_{\pi\ge0}L(\pi)=z_{LP}=\min_{x\in H}cx=w_{\rm col}.
--   $$
--   There exist a minimizing $x^*\in H$ represented in the full master, a maximizing nonnegative multiplier $\pi^*$, and a point $y^*\in Y$ minimizing the Lagrangian at $\pi^*$. The LP supremum is also asserted to be attained. The convexified optimizer $x^*$ is not required to lie in $Y$.
--
--   This identifies the common convexification bound claimed for Lagrangian relaxation, the full column master, and tight reformulation.
--
--   **Formalization Note** The faithful goal retains the maximum definition of the LP bound from p. 198, to which p. 201 explicitly refers. That inherited clause is false (F3); the separately labeled correction uses a minimum. Rationality of $A,b$ makes explicit the rational integer-program convention underlying polyhedrality of the integer hull; $c,D,d,B,e$ remain real. Extended-real infima handle unbounded subproblems without assigning them zero; all finite optimum and multiplier attainments are explicit. The master includes arbitrary recession rays, hence also extreme rays, and permits an empty ray family for bounded cases.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, p. 201 (PDF 215), Theorem 6.5; Sections 6.3.1–6.3.2, pp. 197–201

import Mathlib

namespace PochetWolsey.Decomposition

theorem lagrangian_convexified_bound {n m q t : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (D : Matrix (Fin q) (Fin n) ℝ) (d : Fin q → ℝ)
    (c : Fin n → ℝ)
    (B : Matrix (Fin t) (Fin n) ℝ) (e : Fin t → ℝ) :
    let Y : Set (Fin n → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      (∀ i, (b i : ℝ) ≤ ∑ j, (A i j : ℝ) * x j) ∧
      (∀ j, ∃ z : ℤ, x j = (z : ℝ))}
    let PZ : Set (Fin n → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      ∀ i, d i ≤ ∑ j, D i j * x j}
    let H := convexHull ℝ Y ∩ PZ
    let PYtight : Set (Fin n → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      ∀ i, e i ≤ ∑ j, B i j * x j}
    let cost : (Fin n → ℝ) → ℝ := fun x => ∑ j, c j * x j
    let lag : (Fin q → ℝ) → (Fin n → ℝ) → ℝ := fun π x =>
      cost x + ∑ i, π i * (d i - ∑ j, D i j * x j)
    let L : (Fin q → ℝ) → EReal := fun π =>
      sInf ((fun x => (lag π x : EReal)) '' Y)
    let master : Set (Fin n → ℝ) := {x | x ∈ PZ ∧
      ∃ (k r : ℕ) (v : Fin k → (Fin n → ℝ))
        (u : Fin r → (Fin n → ℝ)) (lam : Fin k → ℝ) (μ : Fin r → ℝ),
        (∀ a, v a ∈ Y) ∧
        (∀ a, u a ≠ 0 ∧ (∀ j, 0 ≤ u a j) ∧
          ∀ i, 0 ≤ ∑ j, (A i j : ℝ) * u a j) ∧
        (∀ a, 0 ≤ lam a) ∧ (∑ a, lam a) = 1 ∧ (∀ a, 0 ≤ μ a) ∧
        x = (fun j => (∑ a, lam a * v a j) + ∑ a, μ a * u a j)}
    let w : EReal := sInf ((fun x => (cost x : EReal)) '' H)
    let zLP : EReal := sSup ((fun x => (cost x : EReal)) '' (PYtight ∩ PZ))
    PYtight = convexHull ℝ Y → H.Nonempty → BddBelow (cost '' H) →
    ∃ (xstar ystar : Fin n → ℝ) (πstar : Fin q → ℝ),
      xstar ∈ H ∧ (∀ x ∈ H, cost xstar ≤ cost x) ∧
      (∀ i, 0 ≤ πstar i) ∧ ystar ∈ Y ∧
      (∀ y ∈ Y, lag πstar ystar ≤ lag πstar y) ∧
      w = (cost xstar : EReal) ∧
      w = L πstar ∧ (∀ π : Fin q → ℝ, (∀ i, 0 ≤ π i) → L π ≤ L πstar) ∧
      w = zLP ∧ w = sInf ((fun x => (cost x : EReal)) '' master) ∧
      xstar ∈ master ∧
      ∃ xmax ∈ PYtight ∩ PZ, (∀ x ∈ PYtight ∩ PZ, cost x ≤ cost xmax) ∧
        zLP = (cost xmax : EReal) := by sorry

end PochetWolsey.Decomposition
