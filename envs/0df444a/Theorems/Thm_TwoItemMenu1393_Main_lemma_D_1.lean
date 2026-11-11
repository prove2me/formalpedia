-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_lemma_D_1
-- name    : TwoItemMenu1393.Main.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:24.429573+00:00
-- url     : https://prove2.me/theorems/559e1602-4678-46f8-bacf-6b7eee421c6f
-- title:
--   Lemma D.1 — Finite positive certificate identity
-- statement:
--   Let $V\subset[0,1]^2$ be finite. Let $w_v,k_v,\lambda_{vt}\ge0$ and $r_v\in[0,\infty)^2$ satisfy, for each $v\in V$,
--   $$\sum_t\lambda_{tv}-\sum_t\lambda_{vt}=w_v-k_v,\qquad w_vv=\sum_t\lambda_{vt}(t-v)+r_v.$$
--   Let an admissible mechanism $(U,g^*)$ have zero utility wherever $k_v>0$, tight IC on every edge of positive multiplier, and $g_i^*(v)=1$ wherever $r_{v,i}>0$. If $S=\sum_vk_v>0$, then $\sum_vw_v/S=1$, the masses $w_v/S$ define a probability law $F$ on $V$, and $(U,g^*)$ is optimal. Every admissible competitor obeys
--   $$\mathrm{OPT}(F)-\mathrm{Rev}_F(u,g)=S^{-1}\left(\sum_{v,t}\lambda_{vt}[u(t)-u(v)-g(v)\cdot(t-v)]+\sum_vk_vu(v)+\sum_vr_v\cdot(\mathbf1-g(v))\right).$$
--   This identity relates actual payments and allocations, including at atoms, to incentive, participation and feasibility slack.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
--   - encoding: Borel probability laws on the type square → ambient Borel measures with total mass one and zero mass off the square; reason: pushforward along the square inclusion gives precisely the same laws and integrals
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Lemma D.1, p. 23–24. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=23

import Definitions.Def_TwoItemMenu1393_Main_Certificate
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Lemma D.1, p. 23–24.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem lemma_D_1 (V : Finset Vec) (w k : Vec → ℝ)
    (lam : Vec → Vec → ℝ) (r : Vec → Vec) (Ustar : Mechanism)
    (hV : ∀ v ∈ V, v ∈ square 1)
    (hpos : (∀ v ∈ V, 0 ≤ w v ∧ 0 ≤ k v ∧ ∀ i, 0 ≤ r v i) ∧
      ∀ v ∈ V, ∀ t ∈ V, 0 ≤ lam v t)
    (hbal : ∀ v ∈ V,
      (∑ t ∈ V, lam t v) - (∑ t ∈ V, lam v t) = w v - k v ∧
      w v • v = (∑ t ∈ V, lam v t • (t-v)) + r v)
    (hU : Admissible Ustar)
    (htight : (∀ v ∈ V, 0 < k v → Ustar.u v = 0) ∧
      (∀ v ∈ V, ∀ t ∈ V, 0 < lam v t → slack Ustar v t = 0) ∧
      ∀ v ∈ V, ∀ i, 0 < r v i → Ustar.g v i = 1)
    (hS : 0 < ∑ v ∈ V, k v) :
    let S := ∑ v ∈ V, k v
    let F := finiteLaw V w S
    (∑ v ∈ V, w v / S) = 1 ∧ Law F ∧ FiniteSupport F ∧
      revenue F Ustar = optimum F ∧
      ∀ M : Mechanism, Admissible M →
        optimum F - revenue F M =
          ((∑ v ∈ V, ∑ t ∈ V, lam v t * slack M v t) +
           (∑ v ∈ V, k v * M.u v) +
           (∑ v ∈ V, dot (r v) (vec 1 1 - M.g v))) / S := by sorry

end TwoItemMenu1393.Main
