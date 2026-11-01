-- Prove2me | Theorems.Thm_RedundancyHT_sandwich
-- name    : RedundancyHT.sandwich
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:49.835857+00:00
-- url     : https://prove2.me/theorems/b9e1458e-67af-4ad5-b263-04373c420aa9
-- title:
--   Appendix C.1, p.31: the sandwich between the transforms of $\tilde Q_S$ and $Q_S$
-- statement:
--   In every reachable state of the cancel-on-start queue, $\tilde Q_S\le Q_S\le\tilde Q_S+N$. Consequently, for $t\ge0$ and $\lambda<\lambda^*$,
--   $$\prod_{S\in\mathcal S}e^{-(1-\frac{\lambda}{\lambda^*})t_SN}\;\mathbb E\Bigl[\prod_{S\in\mathcal S}e^{-(1-\frac{\lambda}{\lambda^*})t_S\tilde Q_S}\Bigr]\le\mathbb E\Bigl[\prod_{S\in\mathcal S}e^{-(1-\frac{\lambda}{\lambda^*})t_SQ_S}\Bigr]\le\mathbb E\Bigl[\prod_{S\in\mathcal S}e^{-(1-\frac{\lambda}{\lambda^*})t_S\tilde Q_S}\Bigr],$$
--   and the deterministic product on the left tends to one as $\lambda\uparrow\lambda^*$.
--
--   So the limit of the waiting-job counts carries over to the total job counts.
--
--   Differences from the source:
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - encoding: for c.o.s. the state descriptor (c;u) omits the jobs in service, so Q_S is not a function of it → laws of the published full QueueState and the count cosCount, which includes jobs in service; reason: Q_S counts jobs in service (p.9)
--   - reading: the subset 𝒯* that maximizes the capacity ratio is unique, i.e., the vector of critical arrival rates can reach any point on the boundary except for its extreme vertices → IsCriticalSubset, the first sentence of Assumption 3; reason: the clause after i.e. is not equivalent: with N = 3, S_i = {i}, p_1/µ_1 = p_2/µ_2 > p_3/µ_3 the maximizer is not unique and the critical point is not a vertex
--   - reading: the stationary distribution, whose existence and uniqueness are taken for granted → every stationary law at the given λ; reason: the laws exist (the goal proves it) and two servers compatible with no type make the c.o.s. law non-unique, so the universal statement covers the source's law in every case
--   - encoding: continuous-time Markov processes → uniformized EventChain with null events and its stationary laws; reason: uniformization does not change stationary laws, because the total clock rate is constant
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Appendix C.1, display below (38), p.31

import Definitions.Def_RedundancyHT_IsCriticalSubset
import Definitions.Def_RedundancyHT_lamStar
import Definitions.Def_RedundancyHT_load
import Definitions.Def_RedundancyHT_cosCount
import Definitions.Def_RedundancyHT_cosWait
import Definitions.Def_RedundancyHT_scaledLaw
import Definitions.Def_RedundancyHT_laplace

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The sandwich between `Q̃_S` and `Q_S`** (arXiv:2005.14566v5, Appendix C.1, p.31): on reachable
states at most `N` jobs of a type are in service, the transforms of the scaled counts satisfy the
two printed inequalities, and the deterministic factor tends to one.

**Formalization Note.** `stationary` makes the law vanish off the reachable states, which is where
the bounds on the counts hold. -/
theorem sandwich {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (T : Finset (Fin n)) (hT : IsCriticalSubset D T) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (∀ q, Reachable D q → ∀ i, cosWait q i ≤ cosCount q i ∧ cosCount q i ≤ cosWait q i + m) ∧
      (∀ (lam : ℝ) (p : QueueState n m → ℝ≥0∞), 0 < lam → lam < lamStar D T →
        stationary D (load D lam) p →
        (∏ i, Real.exp (-(1 - lam / lamStar D T) * t i * (m : ℝ))) *
            laplace (scaledLaw p cosWait (1 - lam / lamStar D T)) t ≤
          laplace (scaledLaw p cosCount (1 - lam / lamStar D T)) t ∧
        laplace (scaledLaw p cosCount (1 - lam / lamStar D T)) t ≤
          laplace (scaledLaw p cosWait (1 - lam / lamStar D T)) t) ∧
      Tendsto (fun lam => ∏ i, Real.exp (-(1 - lam / lamStar D T) * t i * (m : ℝ)))
        (𝓝[<] lamStar D T) (𝓝 1) := by sorry

end RedundancyHT
