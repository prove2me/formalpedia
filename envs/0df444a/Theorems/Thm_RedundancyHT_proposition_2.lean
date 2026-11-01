-- Prove2me | Theorems.Thm_RedundancyHT_proposition_2
-- name    : RedundancyHT.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:45.101978+00:00
-- url     : https://prove2.me/theorems/d68dd183-96c3-48f4-ad57-073bd6d6fd64
-- title:
--   Proposition 2, p.33: the joint PGF of the c.o.s. waiting-job counts
-- statement:
--   Let $\lambda>0$ satisfy the stability conditions, and let $(\tilde Q_S)_{S\in\mathcal S}$ count the waiting jobs under a stationary law of the cancel-on-start queue. For every complex vector $z$ with $|z_S|\le1$,
--   $$\mathbb E\Bigl[\prod_{S\in\mathcal S}z_S^{\tilde Q_S}\Bigr]=\frac{g(z)}{g(\mathbf 1)},$$
--   where
--   $$g(z)=\sum_{L=0}^{N}\sum_{u\in\mathcal N_L}\prod_{l=1}^{L}\frac{\mu_{u_l}}{\lambda_{\mathcal C(u_1,\dots,u_l)}}\sum_{m=0}^{|\mathcal S|}\sum_{S\in\mathcal S_m^{u}}\prod_{j=1}^{m}\frac{N\lambda p_{S_j}z_{S_j}}{\mu(S_1,\dots,S_j)}\Bigl(1-\frac{N\lambda}{\mu(S_1,\dots,S_j)}\sum_{i=1}^{j}p_{S_i}z_{S_i}\Bigr)^{-1}.$$
--   Here $\mathcal N_L$ is the set of ordered vectors of $L$ idle servers, and $\mathcal S_m^{u}$ the set of ordered vectors of $m$ different job types not compatible with the servers in $u$.
--
--   This is the analogue of Proposition 1 that gives the direct proof for cancel-on-start.
--
--   Differences from the source:
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - reading: u runs over the idle servers, with division by λ_𝒞(u_1,…,u_l) → u lists the useful idle servers only (idle.filter useful); reason: with every server useful this is the printed list; a server compatible with no type would give λ_𝒞 = 0, and it has no effect on the system
--   - encoding: the stability conditions (1) and (2) → StabilityOne, i.e. (1); reason: (1) and (2) are equivalent, which is equations_1_2
--   - reading: one printed product over j with the parenthesis inside it → the product covers both factors; reason: compare (10) and the three-step proof of Proposition 1 that the proof invokes, p.34
--   - encoding: entries |z_S| ≤ 1 → z : Fin n → ℂ with ‖z i‖ ≤ 1; reason: this is the page's condition; real z is a special case
--   - encoding: a sum and a quotient that are tacitly well defined → the conclusion also asserts summability and that every inverted quantity is non-zero; reason: Lean's tsum and inverse return junk otherwise; these are added conclusions and exclude nothing
--   - reading: the stationary distribution, whose existence and uniqueness are taken for granted → every stationary law at the given λ; reason: the laws exist (the goal proves it) and two servers compatible with no type make the c.o.s. law non-unique, so the universal statement covers the source's law in every case
--   - encoding: continuous-time Markov processes → uniformized EventChain with null events and its stationary laws; reason: uniformization does not change stationary laws, because the total clock rate is constant
--   - encoding: for c.o.s. the state descriptor (c;u) omits the jobs in service, so Q_S is not a function of it → laws of the published full QueueState and the count cosWait of waiting jobs; reason: Q̃_S counts waiting jobs (p.9, p.33), which the full state determines
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Proposition 2, p.33

import Definitions.Def_RedundancyHT_StabilityOne
import Definitions.Def_RedundancyHT_load
import Definitions.Def_RedundancyHT_pgfG
import Definitions.Def_RedundancyHT_cosWait

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **Proposition 2** (arXiv:2005.14566v5, p.33): the joint PGF of the waiting-job counts of c.o.s. is
`g(z)/g(1)`, for complex `z` with `|z_S| ≤ 1`, under every stationary law.

**Formalization Note.** The conclusion also states that every factor inverted in `g` at a type
vector is non-zero, that `g(1) ≠ 0`, and that the series defining the expectation is summable. -/
theorem proposition_2 {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (lam : ℝ) (hlam : 0 < lam) (h : StabilityOne D lam)
    (p : QueueState n m → ℝ≥0∞) (hp : stationary D (load D lam) p)
    (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (∀ (k : ℕ) (S : Fin k ↪ Fin n) (j : Fin k), pgfDen D lam S z j ≠ 0) ∧
      pgfG D lam (fun _ => 1) ≠ 0 ∧
      Summable (fun q : QueueState n m => ((p q).toReal : ℂ) * ∏ i, z i ^ cosWait q i) ∧
      ∑' q : QueueState n m, ((p q).toReal : ℂ) * ∏ i, z i ^ cosWait q i =
        pgfG D lam z / pgfG D lam (fun _ => 1) := by sorry

end RedundancyHT
