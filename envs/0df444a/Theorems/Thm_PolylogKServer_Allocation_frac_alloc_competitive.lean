-- Prove2me | Theorems.Thm_PolylogKServer_Allocation_frac_alloc_competitive
-- name    : PolylogKServer.Allocation.frac_alloc_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:49:22.34799+00:00
-- url     : https://prove2.me/theorems/ba300cc1-aebe-4a69-a97d-c9777027b51b
-- title:
--   Theorem 5 — a (1+ε, O(log(k/ε)))-competitive fractional allocation algorithm on a weighted star
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $0<\varepsilon\le1$ and consider any instance of the fractional allocation problem on a weighted star: $d$ locations with weights $w_i>0$, $k\ge2$ servers, an initial quota $\kappa(0)\le k$ and an initial integral configuration $n^0$ with $n^0_i\le k$ and $\sum_i n^0_i\le\kappa(0)$. Then there is an online fractional allocation algorithm that is
--   $$
--   \big(1+\varepsilon,\ C\log(k/\varepsilon)\big)\text{-competitive},
--   $$
--   i.e. on every request sequence its hit cost is at most $(1+\varepsilon)(\mathrm{Optcost}+w_{\max}\,g(\kappa))+a$ and its movement cost is at most $C\log(k/\varepsilon)\,(\mathrm{Optcost}+w_{\max}\,g(\kappa))+a$, for a constant $a$ that depends on the instance but not on the requests.
--
--   This is the first ingredient of the paper's main result: through Theorem 6 it yields a fractional k-server algorithm on any well-separated weighted HST.
--
--   **Formalization Note** The $O(\cdot)$ is a universal constant $C$ quantified before $\varepsilon$ and the instance. The range $0<\varepsilon\le1$ is that of Theorem 14 ($\varepsilon=0$ makes $\log(k/\varepsilon)$ undefined); larger $\varepsilon$ follow from $\varepsilon=1$. The guard $k\ge2$ keeps $\log(k/\varepsilon)\ge\log2>0$. $\mathrm{Optcost}$ is the integral optimum and costs are finite.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, arXiv:1110.1580v1, p. 8, Theorem 5 (precise form: Theorem 14, p. 20)

import Mathlib
import Definitions.Def_PolylogKServer_Allocation_Problem

namespace PolylogKServer.Allocation

/-- **Theorem 5** (arXiv:1110.1580v1, p. 8). There is a universal constant `C > 0` such that for
every `0 < ε ≤ 1` and every instance of the allocation problem on a weighted star (`d`
locations with weights `w i > 0`, `k ≥ 2` servers, initial quota `κ₀ ≤ k`, initial integral
configuration `n₀` with `n₀ i ≤ k` and `∑ n₀ ≤ κ₀`) there is an online fractional allocation
algorithm that is `(1 + ε, C · log(k/ε))`-competitive. -/
theorem frac_alloc_competitive :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (d k : ℕ) (w : Fin d → ℝ) (n₀ : Fin d → ℕ) (κ₀ : ℕ), 2 ≤ k →
        (∀ i, 0 < w i) → (∀ i, n₀ i ≤ k) → ∑ i, n₀ i ≤ κ₀ → κ₀ ≤ k →
        ∃ A : FracAlg d k, A.IsCompetitive w n₀ κ₀ (1 + ε) (C * Real.log (k / ε)) := by sorry

end PolylogKServer.Allocation
