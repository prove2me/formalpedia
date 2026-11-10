-- Prove2me | Theorems.Thm_SunMinCut_Cactus_lemma_2_4
-- name    : SunMinCut.Cactus.lemma_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:22:43.576199+00:00
-- url     : https://prove2.me/theorems/dc040e96-6faa-477e-bd00-c8bdf1fc3e5f
-- title:
--   Lemma 2.4 — capping at c0 preserves λ and σ; 2/9 < ρ ≤ 1
-- statement:
--   Let $G$ be a connected aggregated graph on $n\ge2$ vertices with positive capacities, and let $c_0$ be the capacity of an actual cut with $\lambda\le c_0<9\lambda/4$. Put $v_e=\min(w_e,c_0)$, $q_e=v_e/c_0$ and $\rho=\sigma(G)/c_0$. Then the capped graph $(v_e)$ has the same $\lambda$ and the same $\sigma$ as $G$; consequently $2/9<\rho\le1$, $q(\delta P)\ge\rho(|P|-1)$ for every partition $P$ of $V$, and $q(C)\le2\rho$ for every minimum cut $C$ of $G$.
--
--   Differences from the source: none.
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, Lemma 2.4, p. 9

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph

namespace SunMinCut.Cactus

/-- **Lemma 2.4**, Sun 2026, doi:10.5281/zenodo.23915020, p. 9: let `c₀` be the capacity of an
actual cut with `λ ≤ c₀ < 9λ/4`, `v_e = min(w_e, c₀)`, `q_e = v_e/c₀` and `ρ = σ/c₀`. Capping at
`c₀` preserves `λ` and `σ`; consequently `2/9 < ρ ≤ 1`, `q(δP) ≥ ρ(|P| − 1)` for every partition
`P`, and `q(C) ≤ 2ρ` for every minimum cut `C`. -/
theorem lemma_2_4 (n m : ℕ) (hn : 2 ≤ n) (G : Graph n m) (hpos : Positive G)
    (hconn : Connected G) (hagg : Aggregated G) (c0 : ℝ) (hc0 : CoarseCut G c0) :
    lam (capped G c0) = lam G ∧ sigma (capped G c0) = sigma G ∧
    2 / 9 < rho G c0 ∧ rho G c0 ≤ 1 ∧
    (∀ P : Partition n, rho G c0 * ((P.parts.card : ℝ) - 1) ≤ partCut (rates G c0) P) ∧
    ∀ S : Finset (Fin n), IsMinCut G S → cutw (rates G c0) S ≤ 2 * rho G c0 := by sorry

end SunMinCut.Cactus
