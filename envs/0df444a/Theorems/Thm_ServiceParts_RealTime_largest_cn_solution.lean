-- Prove2me | Theorems.Thm_ServiceParts_RealTime_largest_cn_solution
-- name    : ServiceParts.RealTime.largest_cn_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T00:10:56.272083+00:00
-- url     : https://prove2.me/theorems/a3c75622-2835-4603-8c5d-72c037a6e6cf
-- title:
--   Eq. (10.19) — the largest optimal solution of CN_ijt is max(S̃_ijt, critical fractile)
-- statement:
--   Fix a base $j$ and a period $t$, and write $F(s) = P(X_{ijt} \le s)$ for the distribution function of the cumulative demand and
--   $$p = \frac{b_{ij}}{b_{ij} + h_{ij}}$$
--   for the critical ratio. Then:
--
--   1. there is a least integer $s^0$ with $F(s^0) > p$;
--   2. for this $s^0$, the constrained newsvendor problem $\mathrm{CN}_{ijt}$ (minimize $G_{ijt}(S)$ over integers $S \ge \tilde S_{ijt}$) has
--   $$\hat S_{ijt} = \max\big(\tilde S_{ijt},\ s^0\big)$$
--   as its largest optimal solution.
--
--   In particular the largest optimal solution $\hat S_{ijt}$ used in Theorems 15 and 16 exists and is computed by a critical-fractile rule.
--
--   **Formalization Note** The book writes $\hat S_{ijt} = \max(\tilde S_{ijt}, \arg\min_{S \in \mathcal S} G_{ijt}(S))$ with $\mathcal S = \{\lceil F^{-1}(p) \rceil, \lfloor F^{-1}(p) \rfloor\}$. It does not say which inverse of the discrete distribution function it means or how ties are broken. The statement pins the largest unconstrained minimizer of $G_{ijt}$ to the least integer $s^0$ with $F(s^0) > p$. This is what the book's rule selects when ties go to the larger candidate, as "largest optimal solution" requires.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 237, Eq. (10.19)

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model

open MeasureTheory

namespace ServiceParts.RealTime

/-- Eq. (10.19), p. 237: the constrained newsvendor problem `CN_{ijt}` has a largest optimal
solution, namely `Ŝ_{ijt} = max(S̃_{ijt}, s⁰)`, where `s⁰` is the least integer `s` with
`F_{X_{ijt}}(s) > b_{ij}/(b_{ij} + h_{ij})` (the integer critical fractile of the demand). -/
theorem largest_cn_solution {J : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) :
    (∃ s0 : ℤ, IsLeast {s : ℤ | M.b j / (M.b j + M.h j) < M.demandCDF j t s} s0) ∧
      ∀ s0 : ℤ, IsLeast {s : ℤ | M.b j / (M.b j + M.h j) < M.demandCDF j t s} s0 →
        M.IsLargestCNSolution j t (max (M.baseSupply j t) s0) := by sorry

end ServiceParts.RealTime
