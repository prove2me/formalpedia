-- Prove2me | Theorems.Thm_RedundancyHT_proposition_1
-- name    : RedundancyHT.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:05.910557+00:00
-- url     : https://prove2.me/theorems/0706c876-ca95-433c-b435-2906223bb68f
-- title:
--   Proposition 1, p.13: the joint PGF of the c.o.c. job counts
-- statement:
--   Let $\lambda>0$ satisfy the stability conditions, and let $(Q_S)_{S\in\mathcal S}$ have the stationary distribution of the cancel-on-completion chain. For every complex vector $z$ with $|z_S|\le1$,
--   $$\mathbb E\Bigl[\prod_{S\in\mathcal S}z_S^{Q_S}\Bigr]=\frac{f(z)}{f(\mathbf 1)},$$
--   where
--   $$f(z)=1+\sum_{m=1}^{|\mathcal S|}\sum_{S\in\mathcal S_m}\prod_{j=1}^{m}\frac{N\lambda p_{S_j}z_{S_j}}{\mu(S_1,\dots,S_j)}\prod_{j=1}^{m}\Bigl(1-\frac{N\lambda}{\mu(S_1,\dots,S_j)}\sum_{i=1}^{j}p_{S_i}z_{S_i}\Bigr)^{-1}$$
--   and $\mathcal S_m$ is the set of ordered vectors of $m$ different job types.
--
--   This closed form turns the infinite sum over sequences into a finite sum, which makes the term-by-term heavy-traffic limit possible.
--
--   Differences from the source:
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - encoding: the stability conditions (1) and (2) → StabilityOne, i.e. (1); reason: (1) and (2) are equivalent, which is equations_1_2
--   - encoding: entries |z_S| ≤ 1 → z : Fin n → ℂ with ‖z i‖ ≤ 1; reason: this is the page's condition; real z is a special case
--   - encoding: a sum and a quotient that are tacitly well defined → the conclusion also asserts summability and that every inverted quantity is non-zero; reason: Lean's tsum and inverse return junk otherwise; these are added conclusions and exclude nothing
--   - encoding: continuous-time Markov processes → uniformized EventChain with null events and its stationary laws; reason: uniformization does not change stationary laws, because the total clock rate is constant
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Proposition 1, displays (9), (10), p.13

import Definitions.Def_RedundancyHT_cocStationary
import Definitions.Def_RedundancyHT_StabilityOne
import Definitions.Def_RedundancyHT_load
import Definitions.Def_RedundancyHT_pgfSum

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **Proposition 1** (arXiv:2005.14566v5, (9), (10), p.13): the joint PGF of the c.o.c. job counts is
`f(z)/f(1)`, for complex `z` with `|z_S| ≤ 1`.

**Formalization Note.** `f = pgfSum D lam Finset.univ`, whose `k = 0` term is the leading `1` of (10).
The conclusion also states that every factor inverted in (10) is non-zero, that `f(1) ≠ 0`, and that
the series defining the expectation is summable. -/
theorem proposition_1 {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (lam : ℝ) (hlam : 0 < lam) (h : StabilityOne D lam)
    (p : List (Fin n) → ℝ≥0∞) (hp : cocStationary D (load D lam) p)
    (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (∀ (k : ℕ) (S : Fin k ↪ Fin n) (j : Fin k), pgfDen D lam S z j ≠ 0) ∧
      pgfSum D lam Finset.univ (fun _ => 1) ≠ 0 ∧
      Summable (fun c : List (Fin n) => ((p c).toReal : ℂ) * ∏ i, z i ^ c.count i) ∧
      ∑' c : List (Fin n), ((p c).toReal : ℂ) * ∏ i, z i ^ c.count i =
        pgfSum D lam Finset.univ z / pgfSum D lam Finset.univ (fun _ => 1) := by sorry

end RedundancyHT
