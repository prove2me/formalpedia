-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_lemma_D_2
-- name    : TwoItemMenu1393.Main.lemma_D_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:33.568381+00:00
-- url     : https://prove2.me/theorems/e99b6fa9-f5d0-45eb-8def-b60c50a65fd2
-- title:
--   Lemma D.2 — Positive lattice weights and inlet balance
-- statement:
--   For the owned-vertex grid $G_h$ and coefficients $\beta_{vt}$ of (17), there are positive constants $c_1,C_1,c_2,c_3,c_4,c_b,h_0$, independent of $h$, such that every $0<h<h_0$ has weights and nonnegative inlets with
--   $$c_1h^2\le W_v\le C_1h^2,\quad \sum_t\beta_{vt}(t-v)=v,\quad K_v+\sum_{u\in G_h}W_u\beta_{uv}-W_v\sum_t\beta_{vt}=W_v.$$
--   Every one of the four outgoing coefficients is at least $c_3/h$, including coefficients whose targets lie off $G_h$. Moreover, $c_4\le\sum_vK_v\le c_2$ and the positive inlets occupy at most $c_b/h$ boundary vertices, each with a missing incoming lattice predecessor. The weights are the explicit positive-part/forward-recurrence construction of pp. 25–26. These estimates provide the uniform masses and multipliers needed for radial completion.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
--   - encoding: existence of weights, inlets and coefficients, with boundary support O(h⁻¹) → the explicit equations (17)–(19) construction, a bound c_b/h, and missing-predecessor boundary support; reason: the proof defines these witnesses and identifies this boundary support; all constants are quantified before h
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Lemma D.2, p. 24. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=24

import Definitions.Def_TwoItemMenu1393_Main_Lattice
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Lemma D.2, p. 24.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem lemma_D_2 :
    ∃ c₁ C₁ c₂ c₃ c₄ cb h₀ : ℝ,
      0 < c₁ ∧ 0 < C₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧ 0 < cb ∧ 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        (∀ o ∈ grid h, c₁*h^2 ≤ weights h o ∧ weights h o ≤ C₁*h^2 ∧
          0 ≤ inlet h o ∧
          (∑ j : Fin 4, beta h o j • (target h o j - ownedPoint h o)) = ownedPoint h o ∧
          inlet h o + (∑ p ∈ grid h, weights h p * betaInto h p (ownedPoint h o)) -
            weights h o * betaTotal h o = weights h o ∧
          ∀ j : Fin 4, c₃/h ≤ beta h o j) ∧
        c₄ ≤ (∑ o ∈ grid h, inlet h o) ∧ (∑ o ∈ grid h, inlet h o) ≤ c₂ ∧
        (((grid h).filter (fun o => 0 < inlet h o)).card : ℝ) ≤ cb/h ∧
        ∀ o ∈ grid h, 0 < inlet h o → BoundaryInlet h o := by sorry

end TwoItemMenu1393.Main
