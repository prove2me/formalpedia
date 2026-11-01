-- Prove2me | Theorems.Thm_PConeEB_theorem_4_1
-- name    : PConeEB.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:47.341814+00:00
-- url     : https://prove2.me/theorems/e6bfae95-edd5-4e39-9788-26876591b465
-- title:
--   Theorem 4.1 — the exponent $\alpha_z$ is valid for every extreme ray
-- statement:
--   Let $n\ge2$, $p,q\in(1,\infty)$ with $\frac1p+\frac1q=1$, $z\in\partial\mathcal K_q^{n+1}\setminus\{0\}$, $\mathcal F_z:=\{z\}^\perp\cap\mathcal K_p^{n+1}$, $\eta>0$, $\alpha_z$ as in (4.6), and
--   $$
--   \gamma_{z,\eta}:=\inf_v\left\{\frac{\|v-w\|^{\alpha_z}}{\|u-w\|}\ \middle|\ v\in\partial\mathcal K_p^{n+1}\cap B(\eta)\setminus\mathcal F_z,\ w=P_{\{z\}^\perp}v,\ u=P_{\mathcal F_z}w,\ u\ne w\right\}.
--   $$
--   Then $\gamma_{z,\eta}\in(0,\infty]$, and
--   $$
--   \operatorname{dist}(x,\mathcal F_z)\le\max\{2\eta^{1-\alpha_z},2\gamma_{z,\eta}^{-1}\}\cdot\operatorname{dist}(x,\mathcal K_p^{n+1})^{\alpha_z}\quad\text{whenever }x\in\{z\}^\perp\cap B(\eta).
--   $$
--
--   This is the upper bound half of the main theorem at the level of a single face.
--
--   Differences from the source:
--   - encoding: (4.7) → gammaZ with g = fun t => |t| ^ alphaZ p z and kappaZ with α = alphaZ p z; reason: (4.7) is (2.13) for this g, with the norms of w − v and u − w written in the other order
--   - encoding: γ_{z,η} ∈ (0, ∞], with inf ∅ = +∞ → gammaZ in ENNReal, 0 < gammaZ K z g η; κ_{z,η} the real number kappaZ, with γ⁻¹ read as 0 at γ = ⊤; reason: the paper's own convention γ_{z,0} = ∞; kappaZ is used only under 0 < gammaZ
--   - encoding: ℝ^{n+1}, x₀, x̄, ‖x̄‖_p, ∂ → RR n = EuclideanSpace ℝ (Fin (n + 1)), x 0, x i.succ for i : Fin n, pNorm with real rpow, frontier; reason: Lean conventions; same instances
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Theorem 4.1, (4.7), p.19

import Mathlib
import Definitions.Def_PConeEB_hyperplane
import Definitions.Def_PConeEB_pCone
import Definitions.Def_PConeEB_alphaZ
import Definitions.Def_PConeEB_gammaZ
import Definitions.Def_PConeEB_kappaZ

namespace PConeEB

/-- Theorem 4.1. Let `n ≥ 2`, `1/p + 1/q = 1`, `z ∈ ∂K_q^{n+1} \ {0}`, `F_z := {z}^⊥ ∩ K_p^{n+1}`,
`η > 0`, and `γ_{z,η}` the infimum (4.7) with exponent `α_z` of (4.6). Then `γ_{z,η} ∈ (0, ∞]` and
`dist(x, F_z) ≤ max{2 η^{1-α_z}, 2 γ_{z,η}⁻¹} · dist(x, K_p^{n+1})^{α_z}` for `x ∈ {z}^⊥ ∩ B(η)`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Theorem 4.1, (4.7), p.19.

**Formalization Note.** (4.7) is `gammaZ` with `g = |·|^{α_z}`: it writes `‖v - w‖`, `‖u - w‖` for
the same quantities. -/
theorem theorem_4_1 {n : ℕ} (hn : 2 ≤ n) {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    {z : RR n} (hz : z ∈ frontier (pCone n q)) (hz0 : z ≠ 0) {η : ℝ} (hη : 0 < η) :
    0 < gammaZ (pCone n p) z (fun t => |t| ^ alphaZ p z) η ∧
      ∀ x ∈ hyperplane z, ‖x‖ ≤ η →
        Metric.infDist x (pCone n p ∩ hyperplane z) ≤
          kappaZ (pCone n p) z (fun t => |t| ^ alphaZ p z) (alphaZ p z) η *
            Metric.infDist x (pCone n p) ^ alphaZ p z := by sorry

end PConeEB
