-- Prove2me | Theorems.Thm_PolylogKServer_Fractional_kserver_from_allocation
-- name    : PolylogKServer.Fractional.kserver_from_allocation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:07:15.563755+00:00
-- url     : https://prove2.me/theorems/17428d40-0d86-4f33-813e-045dd3c1465c
-- title:
--   Theorem 6 — from allocation to fractional k-server: O(ℓ log(kℓ))-competitive on weighted σ-HSTs of depth ℓ
-- statement:
--   For every $c_0>0$ there is a constant $C>0$ with the following property. Let $k\ge2$ and suppose that for every $0<\varepsilon\le1$ and every instance of the fractional allocation problem on a weighted star with $k$ servers (any number $d$ of locations, any weights $w_i>0$, any initial quota and initial configuration) there is a $(1+\varepsilon,\ c_0\log(k/\varepsilon))$-competitive online fractional allocation algorithm. Then for every weighted $\sigma$-HST $T$ of depth $\ell\ge1$ with
--   $$
--   \sigma\ \ge\ C\,\ell\log(k\ell),
--   $$
--   every finite metric space $M$ that is the leaf metric of $T$, and every initial configuration $C_0$ of $k$ servers on distinct points, there is an online fractional k-server algorithm on $T$ from $C_0$ that is
--   $$
--   C\,\ell\log(k\ell)\text{-competitive}
--   $$
--   against the optimal integral offline k-server cost.
--
--   This is the second ingredient of the main result: with Theorem 5 plugged in, it gives a fractional k-server algorithm on the logarithmic-depth weighted HSTs produced by Theorem 8.
--
--   **Formalization Note** The paper's hypothesis reads "$(1+\varepsilon,\log(k/\varepsilon))$-competitive" with no constant; the constant $c_0$ is made explicit and quantified first, and $C$ depends on $c_0$ only, so the statement implies the literal one and composes with Theorem 5. One constant $C$ serves for both the $\Omega(\cdot)$ condition on $\sigma$ and the $O(\cdot)$ ratio. The hypothesis is the published allocation model with finite cost vectors; the construction of §4 uses infinite hit costs (Observation 17), which a proof has to emulate.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, arXiv:1110.1580v1, p. 8, Theorem 6 (restated pp. 26–27)

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_PolylogKServer_HST_Tree
import Definitions.Def_PolylogKServer_Allocation_Problem
import Definitions.Def_PolylogKServer_Fractional_KServer

namespace PolylogKServer.Fractional

open PolylogKServer.HST PolylogKServer.Allocation

/-- **Theorem 6** (arXiv:1110.1580v1, p. 8, restated pp. 26–27), with the constant of the
hypothesis made explicit. For every `c₀ > 0` there is `C > 0` such that for every `k ≥ 2`:
if for every `0 < ε ≤ 1` and every allocation instance on a weighted star with `k` servers
there is a `(1 + ε, c₀ · log(k/ε))`-competitive online fractional allocation algorithm, then for
every weighted σ-HST `T` of depth `ℓ ≥ 1` with `σ ≥ C · ℓ · log(kℓ)`, every finite metric space
`M` that is the leaf metric of `T`, and every injective initial configuration `C₀`, there is a
`C · ℓ · log(kℓ)`-competitive online fractional k-server algorithm on `T` from `C₀`. -/
theorem kserver_from_allocation :
    ∀ c₀ : ℝ, 0 < c₀ → ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ (d : ℕ) (w : Fin d → ℝ) (n₀ : Fin d → ℕ) (κ₀ : ℕ),
          (∀ i, 0 < w i) → (∀ i, n₀ i ≤ k) → ∑ i, n₀ i ≤ κ₀ → κ₀ ≤ k →
          ∃ A : FracAlg d k, A.IsCompetitive w n₀ κ₀ (1 + ε) (c₀ * Real.log (k / ε))) →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V) (σ : ℝ) (ℓ : ℕ),
        1 ≤ ℓ → T.height = ℓ → T.IsWeightedHST σ →
        C * ℓ * Real.log (k * ℓ) ≤ σ →
        ∀ (M : Type) [MetricSpace M] [Fintype M] (e : M ≃ T.Leaf),
          T.IsLeafMetric M e →
          ∀ C₀ : KServer.Config k M, Function.Injective C₀ →
          ∃ F : FracKServerAlg k M,
            F.IsCompetitiveFrom T e C₀ (C * ℓ * Real.log (k * ℓ)) := by sorry

end PolylogKServer.Fractional
