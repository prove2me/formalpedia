-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_lemma_4_2
-- name    : TwoItemMenu1393.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:06.205288+00:00
-- url     : https://prove2.me/theorems/2c341cf9-60c6-4354-8878-937de09fe513
-- title:
--   Lemma 4.2 — Quadratic limit and derivative convergence
-- statement:
--   Let $h_n>0$ tend to zero, and let $(u_n,g_n)$ be admissible mechanisms with $L_{h_n}(u_n,g_n)/h_n\to0$. For every strictly increasing subsequence index map $\sigma$ and every uniform limit $u$ of $u_{\sigma(n)}$ on the type square,
--   $$u(v)=Q(v)\quad(v\in\mathcal D),\qquad D\Gamma_{h_{\sigma(n)}}\longrightarrow I\quad\text{in Lebesgue measure on every compact }K\subset\mathcal D.$$
--   The interpolation domain eventually contains every such $K$. Convergence in measure means that the area where the operator-norm error exceeds any fixed positive threshold tends to zero. Both conclusions hold along the same arbitrary uniformly convergent subsequence. This supplies the derivative control needed for counting menu vertices.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
--   - encoding: subsequence and local convergence in measure → an arbitrary StrictMono index map and convergence of Lebesgue exceptional-set measures for every compact set and every positive threshold; reason: these express exactly the subsequence and convergence-in-measure quantifiers, including eventual field-domain coverage
--   - encoding: the trianglewise Jacobian → the explicit interpolation matrix, set to zero on triangle boundaries; reason: boundaries have zero planar area; convergence in measure is unchanged
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Lemma 4.2, p. 12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=12

import Definitions.Def_TwoItemMenu1393_Main_Fields
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Lemma 4.2, p. 12.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem lemma_4_2 (hs : ℕ → ℝ) (Ms : ℕ → Mechanism)
    (hpos : ∀ n, 0 < hs n) (hzero : Filter.Tendsto hs Filter.atTop (nhds 0))
    (hadm : ∀ n, Admissible (Ms n))
    (hloss : Filter.Tendsto (fun n => loss (hs n) (Ms n) / hs n) Filter.atTop (nhds 0)) :
    ∀ (σ : ℕ → ℕ) (u : Vec → ℝ), StrictMono σ →
      TendstoUniformlyOn (fun n => (Ms (σ n)).u) u Filter.atTop (square 1) →
      (∀ v ∈ sector, u v = Q v) ∧
      ∀ K : Set Vec, IsCompact K → K ⊆ sector →
        (∀ᶠ n in Filter.atTop, K ⊆ fieldDomain (hs (σ n))) ∧
        ∀ α : ℝ, 0 < α →
          Filter.Tendsto
            (fun n => volume (K ∩ {v | α < ‖fieldDerivative (hs (σ n)) (Ms (σ n)) v -
              ContinuousLinearMap.id ℝ Vec‖})) Filter.atTop (nhds 0) := by sorry

end TwoItemMenu1393.Main
