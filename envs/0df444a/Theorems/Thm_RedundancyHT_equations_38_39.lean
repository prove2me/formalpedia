-- Prove2me | Theorems.Thm_RedundancyHT_equations_38_39
-- name    : RedundancyHT.equations_38_39
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:01.105983+00:00
-- url     : https://prove2.me/theorems/f02deb8a-f353-4783-855f-c9a0af5ba594
-- title:
--   (38), (39), pp.31–32: the limit of the c.o.s. waiting-job counts
-- statement:
--   Let $\mathcal T^*$ be the critical subset, and let $\tilde Q_S$ be the number of waiting type-$S$ jobs under a stationary law of the cancel-on-start queue. With $z_S=\exp(-(1-\lambda/\lambda^*)t_S)$ and $t_S\ge0$,
--   $$\mathbb E\Bigl[\prod_{S\in\mathcal S}z_S^{\tilde Q_S}\Bigr]\longrightarrow\Bigl(1+\sum_{S\in\mathcal T^*}\frac{p_S}{p_{\mathcal T^*}}t_S\Bigr)^{-1},\tag{39}$$
--   and consequently
--   $$\Bigl(1-\frac{\lambda}{\lambda^*}\Bigr)(\tilde Q_S)_{S\in\mathcal S}\xrightarrow{d}\Bigl(\mathrm{Exp}(1)\Bigl(\frac{p_S}{p_{\mathcal T^*}}\Bigr)_{S\in\mathcal T^*},(0)_{S\notin\mathcal T^*}\Bigr)\tag{38}$$
--   as $\lambda\uparrow\lambda^*$.
--
--   Since the number of jobs in service is bounded, this yields the cancel-on-start half of the main theorem.
--
--   Differences from the source:
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - reading: the subset 𝒯* that maximizes the capacity ratio is unique, i.e., the vector of critical arrival rates can reach any point on the boundary except for its extreme vertices → IsCriticalSubset, the first sentence of Assumption 3; reason: the clause after i.e. is not equivalent: with N = 3, S_i = {i}, p_1/µ_1 = p_2/µ_2 > p_3/µ_3 the maximizer is not unique and the critical point is not a vertex
--   - reading: the stationary distribution, whose existence and uniqueness are taken for granted → every family of stationary laws on (0, λ*); reason: the laws exist (the goal proves it) and two servers compatible with no type make the c.o.s. law non-unique, so the universal statement covers the source's law in every case
--   - encoding: continuous-time Markov processes → uniformized EventChain with null events and its stationary laws; reason: uniformization does not change stationary laws, because the total clock rate is constant
--   - encoding: for c.o.s. the state descriptor (c;u) omits the jobs in service, so Q_S is not a function of it → laws of the published full QueueState and the count cosCount, which includes jobs in service; reason: Q_S counts jobs in service (p.9)
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, display (38), p.31, and display (39), p.32

import Definitions.Def_RedundancyHT_IsCriticalSubset
import Definitions.Def_RedundancyHT_lamStar
import Definitions.Def_RedundancyHT_load
import Definitions.Def_RedundancyHT_cosWait
import Definitions.Def_RedundancyHT_scaledLaw
import Definitions.Def_RedundancyHT_limitLaw
import Definitions.Def_RedundancyHT_ConvergesInLaw
import Definitions.Def_RedundancyHT_laplace

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **(38) and (39)** (arXiv:2005.14566v5, pp.31–32): the scaled waiting-job counts of c.o.s. have
the limit transform of (39) and converge in law to the limit vector. -/
theorem equations_38_39 {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (T : Finset (Fin n)) (hT : IsCriticalSubset D T)
    (π : ℝ → QueueState n m → ℝ≥0∞)
    (hπ : ∀ lam, 0 < lam → lam < lamStar D T → stationary D (load D lam) (π lam)) :
    (∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) →
      Tendsto (fun lam => laplace (scaledLaw (π lam) cosWait (1 - lam / lamStar D T)) t)
        (𝓝[<] lamStar D T) (𝓝 (1 + ∑ i ∈ T, pOf D i / pSet D T * t i)⁻¹)) ∧
      ConvergesInLaw (fun lam => scaledLaw (π lam) cosWait (1 - lam / lamStar D T))
        (𝓝[<] lamStar D T) (limitLaw D T) := by sorry

end RedundancyHT
