-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_asymmetric_bound
-- name    : SimplicialIso.Mixing.asymmetric_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:29.600517+00:00
-- url     : https://prove2.me/theorems/c5208eaa-bf85-43c6-80f2-3157be02535e
-- title:
--   p. 18 — ||F(A_0,…,A_d)| − α|A_0|⋯|A_d|/n| ≤ ρ_α√(|A_0||A_d|)|A_1|⋯|A_{d−1}|
-- statement:
--   Let $X$ be a $d$-dimensional complex with a complete skeleton on $n$ vertices, $d\ge1$, let $A_0,\dots,A_d$ be pairwise disjoint sets of vertices, $\alpha\in\mathbb R$, and let $\rho$ satisfy $|\mu|\le\rho$ for every eigenvalue $\mu$ of $\alpha I-\Delta^+$ on $Z_{d-1}$. Then
--   $$\left|\,|F(A_0,A_1,\dots,A_d)|-\frac{\alpha\cdot|A_0|\cdots|A_d|}{n}\right|\le\rho\sqrt{|A_0|\,|A_d|}\;|A_1|\,|A_2|\cdots|A_{d-1}|.$$
--
--   This is the bound obtained from (4.8), (4.9) and (4.11) before symmetrizing over the blocks.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, §4.3, p. 18, the display after (4.11) ('Together (4.8), (4.9) and (4.11) give')

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- p. 18, from (4.8), (4.9) and (4.11): for disjoint `A_0, …, A_d`, if `ρ` bounds the absolute
value of every eigenvalue of `αI − Δ⁺` on `Z_{d-1}`, then
`| |F(A_0, …, A_d)| − α |A_0| ⋯ |A_d| / n | ≤ ρ √(|A_0| |A_d|) |A_1| ⋯ |A_{d-1}|`. -/
theorem asymmetric_bound (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d)
    (A : Fin (d + 1) → Finset (Fin n)) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (α ρ : ℝ)
    (hρ : ∀ μ, IsCycleEigenvalue (α • LinearMap.id - upLap X) μ → |μ| ≤ ρ) :
    |((F X A).card : ℝ) - α * (∏ i, ((A i).card : ℝ)) / n| ≤
      ρ * Real.sqrt (((A 0).card : ℝ) * (A (Fin.last d)).card) *
        ∏ i ∈ univ.filter (fun i : Fin (d + 1) => i ≠ 0 ∧ i ≠ Fin.last d),
          ((A i).card : ℝ) := by sorry

end SimplicialIso.Mixing
