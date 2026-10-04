-- Prove2me | Theorems.Thm_PolylogKServer_Rounding_fractional_to_randomized
-- name    : PolylogKServer.Rounding.fractional_to_randomized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:07:40.375247+00:00
-- url     : https://prove2.me/theorems/1c810f69-fca0-440d-af53-d24f17c3f0d4
-- title:
--   Theorem 7 — on a σ-HST (σ > 5) a c-competitive fractional k-server algorithm yields an O(c)-competitive randomized one
-- statement:
--   For every $\sigma>5$ there is a constant $C>0$ such that the following holds. Let $T$ be a $\sigma$-HST whose leaves form the finite metric space $M$, let $k\in\mathbb N$ and let $C_0$ be an initial configuration of $k$ servers on distinct points. If an online fractional k-server algorithm on $T$ is $c$-competitive from $C_0$ ($c\ge0$), then there is a randomized online k-server algorithm on $M$ that starts at $C_0$ and is
--   $$
--   C\cdot c\text{-competitive}
--   $$
--   against an oblivious adversary: its expected cost on every request sequence $\rho$ is at most $C\,c\cdot\mathrm{OPT}(C_0,\rho)+a$ for a constant $a$ independent of $\rho$.
--
--   This is the rounding step of the main result: fractional solutions on σ-HSTs lose only a constant factor when turned into randomized algorithms.
--
--   **Formalization Note** The randomized algorithm is the published mixed-strategy model `KServer.RandomizedAlgorithm` with `IsCompetitiveFrom` (definition `KServer_randomized`). "With an $O(1)$ factor loss" is rendered as a constant $C$ depending on $\sigma$ only, quantified after $\sigma$ and before everything else. The guard $c\ge0$ is added. The result is for (unweighted) σ-HSTs only, as on p. 9.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, arXiv:1110.1580v1, p. 9, Theorem 7 (§5.2, pp. 36–39)

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized
import Definitions.Def_PolylogKServer_HST_Tree
import Definitions.Def_PolylogKServer_Fractional_KServer

namespace PolylogKServer.Rounding

open PolylogKServer.HST PolylogKServer.Fractional

/-- **Theorem 7** (arXiv:1110.1580v1, p. 9). For every `σ > 5` there is a constant `C > 0`
(depending on `σ` only) such that for every σ-HST `T`, every finite metric space `M` that is the
leaf metric of `T`, every `k` and every injective initial configuration `C₀`: every
`c`-competitive online fractional k-server algorithm on `T` from `C₀` (`c ≥ 0`) can be converted
into a randomized online k-server algorithm on `M` that is `C · c`-competitive from `C₀`. -/
theorem fractional_to_randomized :
    ∀ σ : ℝ, 5 < σ → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M] (e : M ≃ T.Leaf), T.IsLeafMetric M e →
      ∀ (k : ℕ) (C₀ : KServer.Config k M), Function.Injective C₀ →
      ∀ (F : FracKServerAlg k M) (c : ℝ), 0 ≤ c → F.IsCompetitiveFrom T e C₀ c →
        ∃ A : KServer.RandomizedAlgorithm k M, A.IsCompetitiveFrom C₀ (C * c) := by sorry

end PolylogKServer.Rounding
