-- Prove2me | Theorems.Thm_PolyhedralPacking1261_Packing_Supplement_theorem_4
-- name    : PolyhedralPacking1261.Packing.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:41:06.645045+00:00
-- url     : https://prove2.me/theorems/061d7914-5197-4cac-9651-73cdca6f1746
-- title:
--   Theorem 4 — Kakeya volume estimate for angularly separated tubes with arbitrary centers
-- statement:
--   For every $\varepsilon>0$ there is a constant $C_\varepsilon\ge1$ such that the following holds for all $0<\delta\le1$. Let $v_1,\dots,v_m\in S^2$ be unit vectors such that for distinct $i,j$ the unoriented angle between $v_i$ and $v_j$ is at least $\delta$, and let $x_1,\dots,x_m\in\mathbb R^3$ be arbitrary. Then
--
--   $$\mathrm{vol}\Big(\bigcup_{i=1}^m T_\delta(v_i,x_i)\Big)\ \ge\ \frac{\delta^\varepsilon}{C_\varepsilon}\sum_{i=1}^m \mathrm{vol}\big(T_\delta(v_i,x_i)\big),$$
--
--   where $T_\delta(v,x)$ is the open $\delta$-neighbourhood of the unit segment $\{x+tv:|t|\le\frac12\}$.
--
--   This is the global form, without a containing ball and for every $\delta\le1$, of Wang and Zahl's Kakeya volume estimate; the paper derives it from their Theorem 1.2 and uses it in the proof of Theorem 8.
--
--   Differences from the source:
--   - encoding: S², R³, vol, unoriented angle → unit vectors of EuclideanSpace ℝ (Fin 3), Lebesgue measure in [0,∞], min of InnerProductGeometry.angle v w and angle v (−w); reason: Lean conventions; same instances (m = 0 is allowed and trivial)
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, Theorem 4, §1.1, PDF pp.4–5 (printed pp.3–4); proof in Appendix A, PDF pp.25–26 (printed pp.24–25)

import Definitions.Def_PolyhedralPacking1261_Packing_Supplement_Kakeya

set_option autoImplicit false

open MeasureTheory

namespace PolyhedralPacking1261.Packing.Supplement

/-- Theorem 4, PDF pp.4–5 (printed pp.3–4). For every `ε > 0` there is `C_ε ≥ 1` such
that for all `0 < δ ≤ 1`, all unit vectors `v₁,…,v_m` with pairwise unoriented angle at
least `δ`, and all centers `x₁,…,x_m`,
`vol(⋃ T_δ(v_i,x_i)) ≥ (δ^ε / C_ε) Σ vol(T_δ(v_i,x_i))`. -/
theorem theorem_4 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∀ (m : ℕ) (v : Fin m → E3), (∀ i, ‖v i‖ = 1) →
          (∀ i j, i ≠ j → δ ≤ unorientedAngle (v i) (v j)) →
          ∀ x : Fin m → E3,
            ENNReal.ofReal (δ ^ ε / C) * ∑ i, volume (tube δ (v i) (x i)) ≤
              volume (⋃ i, tube δ (v i) (x i)) := by sorry

end PolyhedralPacking1261.Packing.Supplement
