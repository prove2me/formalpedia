-- Prove2me | Theorems.Thm_SupplyChainTheory_disruption_stationary
-- name    : SupplyChainTheory.disruption_stationary
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:48:06.008728+00:00
-- url     : https://prove2.me/theorems/ace15f3a-fb1f-4aa7-b6e0-53968d8a3c07
-- title:
--   Lemma 9.2: the steady-state probabilities of the disruption chain, $\pi_n = \frac{\alpha\beta}{\alpha+\beta}(1-\beta)^{n-1}$ and $F(n) = 1 - \frac{\alpha}{\alpha+\beta}(1-\beta)^n$
-- statement:
--   **Lemma 9.2.** If the disruption probability is $\alpha \in (0, 1]$ and the recovery
--   probability is $\beta \in (0, 1]$, then the distribution $\pi_0 = \beta/(\alpha+\beta)$,
--   $\pi_n = \frac{\alpha\beta}{\alpha+\beta}(1-\beta)^{n-1}$ ($n \ge 1$) is summable with total mass $1$,
--   satisfies the stationary equations of the disruption chain (state $0$ up, state $n \ge 1$ the
--   $n$-th period of a disruption), and its distribution function is
--
--   $$ F(n) = 1 - \frac{\alpha}{\alpha+\beta}(1-\beta)^n, \qquad n \ge 0. $$
--
--   The book omits the proof (Problem 9.10). Down intervals are geometric with parameter $\beta$,
--   and $\pi_0 = \beta/(\alpha+\beta)$ is the long-run fraction of up periods (9.8); the chain's
--   stationarity is what justifies treating $\pi_n$ as the probability that a random period is the
--   $n$-th of a disruption in the cost (9.14).
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 362, Sect. 9.2.2.1, Lemma 9.2: 'Proof. Omitted; see Problem 9.10'; the chain is described on pp. 361-362, Eq. (9.8)-(9.10)

import Definitions.Def_SupplyChainTheory_disruptions

namespace SupplyChainTheory

theorem disruption_stationary (α β : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    Summable (disruptionPmf α β) ∧ (∑' n, disruptionPmf α β n) = 1
      ∧ IsStationary α β (disruptionPmf α β)
      ∧ ∀ n, disruptionCdf α β n = 1 - α / (α + β) * (1 - β) ^ n := by sorry

end SupplyChainTheory
