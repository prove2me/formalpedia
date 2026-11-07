-- Prove2me | Theorems.Thm_TwoBoxMemory_theorem_B_3
-- name    : TwoBoxMemory.theorem_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:51.156595+00:00
-- url     : https://prove2.me/theorems/63349507-6d65-468c-a808-4f075b12a908
-- title:
--   Theorem B.3 — a counted deterministic construction, $\Delta_M\le K M\tau^{H_M}$
-- statement:
--   Throughout, $(r,s,\beta,D)$ is a **non-tie positive saddle with irrational logarithmic failure ratio**: $r,s\in(0,1)$ are the failure probabilities at locations $A$ and $B$ ($p=1-r$, $t=1-s$), $\log r/\log s$ is irrational, $\beta>0$, $\beta r^i\neq s^j$ for all $i,j\ge0$, $u=1/p-H_B>0$, $v=1/t-H_A>0$ and $D>0$; the cost of command $A$ is the saddle cost $C=Dv/u$, and $W$ is the greedy word. For every integer $M\ge2$ there is a deterministic controller with a pure initial label and at most $M$ labels whose worst risk is at most $V+KM\tau^{H_M}$, where
--
--   $$K=K_0\,\frac{\max(C,D)}{\min(p,t)}\,\tau^{-(R+1)} ;$$
--
--   in particular $\Delta_M\le KM\tau^{H_M}$.
--
--   This is the upper half of the arithmetic memory bound.
--
--   Differences from the source:
--   - encoding: $\Delta_M=V_M-V$ with $V_M,V\in[0,\infty]$ → `gap` $=(V_M).\mathrm{toReal}-V.\mathrm{toReal}$; reason: both values are finite for $M\ge1$ (proved in the verification file), so the real difference is exact
--   - encoding: controller risk as the risk (B.4) of the cylinder law $\mu K_{x_0}\cdots K_{x_{h-1}}\mathbf 1$ (p.2) → closed form $\sum_{n\ge0}\mu Q_h^n c$ of Appendix C, p.28; reason: the paper states both forms of the same quantity; every term is nonnegative
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Theorem B.3, (B.12), p.23 (PDF 25); (7.1), p.10 (PDF 12)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
open MeasureTheory

namespace TwoBoxMemory

/-- Theorem B.3 (A counted deterministic construction). At a non-tie positive saddle, for every
integer `M ≥ 2` there is a deterministic controller with a pure initial label and at most `M`
labels whose worst risk is at most `V + K M τ^{H_M}`, `K = K₀ max(C, D)/min(p, t) · τ^{−(R+1)}`;
in particular `Δ_M ≤ K M τ^{H_M}` (B.12).

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Theorem B.3, (B.12), p.23 (PDF 25); (7.1), p.10 (PDF 12).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem theorem_B_3 (r s β D : ℝ) (hS : IsSaddle r s β D) (M : ℕ) (hM : 2 ≤ M) :
    (∃ m ≤ M, ∃ κ : Controller m, IsDeterministic κ ∧
      worstRisk r s (saddleCost r s β D) D κ ≤
        value r s (saddleCost r s β D) D +
          ENNReal.ofReal (K0' r s β (saddleCost r s β D) D * M * tau r s ^ profH (greedyWord r s β) M)) ∧
    gap r s (saddleCost r s β D) D M ≤ K0' r s β (saddleCost r s β D) D * M * tau r s ^ profH (greedyWord r s β) M := by sorry

end TwoBoxMemory
