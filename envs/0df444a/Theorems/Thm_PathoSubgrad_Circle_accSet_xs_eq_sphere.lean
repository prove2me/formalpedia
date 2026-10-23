-- Prove2me | Theorems.Thm_PathoSubgrad_Circle_accSet_xs_eq_sphere
-- name    : PathoSubgrad.Circle.accSet_xs_eq_sphere
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:34.812182+00:00
-- url     : https://prove2.me/theorems/1d7443b9-db0c-48f6-bc19-ee70e64d6638
-- title:
--   §2, p. 5 — the sequence (x_i) is bounded, accumulates on the whole unit circle, and does not converge
-- statement:
--   Let $x_i=[1+(-1)^i/i](\cos\vartheta_i,\sin\vartheta_i)$ with $\vartheta_i=\sum_{k=2}^i 1/(k\log k)$, and let $i_0\ge2$. The sequence $(x_{i_0+k})_{k\ge0}$ is bounded, its accumulation set is the whole unit circle,
--   $$\operatorname{acc}\{x_{i_0+k}\}_k=S^1,$$
--   and it does not converge.
--
--   The radii tend to $1$ while the angles $\vartheta_i$ increase to $+\infty$ by vanishing increments, so the points wind around the circle forever. Together with Proposition 6 (ii) this is the non-convergent bounded subgradient sequence of the example.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 5, §2 (opening paragraph); cf. Figure 1, p. 6

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

open Filter Topology
open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

theorem accSet_xs_eq_sphere (i0 : ℕ) (hi0 : 2 ≤ i0) :
    Bornology.IsBounded (Set.range fun k => xs (i0 + k)) ∧
    accSet (fun k => xs (i0 + k)) = Metric.sphere 0 1 ∧
    ¬ ∃ p, Tendsto (fun k => xs (i0 + k)) atTop (𝓝 p) := by sorry

end PathoSubgrad.Circle
