-- Prove2me | Theorems.Thm_RedundancyHT_stability_iff
-- name    : RedundancyHT.stability_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:04.11855+00:00
-- url     : https://prove2.me/theorems/df10138b-ac4a-4a6d-9a84-8ea7714d2c31
-- title:
--   Assumption 1, p.5: the stability conditions are necessary and sufficient for both mechanisms
-- statement:
--   For $\lambda>0$, the following are equivalent to the stability conditions (1), and hence to (2):
--
--   1. the cancel-on-completion chain has a stationary law;
--   2. the cancel-on-start queue with assignment to the longest idle server has a stationary law.
--
--   The heavy-traffic statement is about stationary laws below $\lambda^*$, so it needs them to exist.
--
--   Differences from the source:
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - reading: the system is stable → the chain has a stationary law; reason: for a countable irreducible class this is positive recurrence, the source's notion of stability
--   - encoding: for c.o.s. the state descriptor (c;u) omits the jobs in service, so Q_S is not a function of it → stationary laws of the published full QueueState (Stable); reason: the full state keeps the jobs in service and has finite fibres over (c;u), so a stationary law exists for one iff for the other
--   - encoding: continuous-time Markov processes → uniformized EventChain with null events and its stationary laws; reason: uniformization does not change stationary laws, because the total clock rate is constant
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Assumption 1, p.5 (the paper cites [2, 28])

import Definitions.Def_RedundancyHT_StabilityOne
import Definitions.Def_RedundancyHT_load
import Definitions.Def_RedundancyHT_cocStationary

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **Assumption 1, last clause** (arXiv:2005.14566v5, p.5): the conditions (1), (2) "have been shown
to be necessary and sufficient conditions for the system to be stable under the c.o.c. or c.o.s.
mechanisms".

**Formalization Note.** Stable means that a stationary law of the chain exists. For c.o.s. this is
the published `Stable`, on the full `QueueState`, which has finite fibres over the descriptor of
(5). By `equations_1_2`, (2) is equivalent to (1). -/
theorem stability_iff {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (lam : ℝ) (hlam : 0 < lam) :
    (StabilityOne D lam ↔ ∃ p, cocStationary D (load D lam) p) ∧
      (StabilityOne D lam ↔ Stable D (load D lam)) := by sorry

end RedundancyHT
