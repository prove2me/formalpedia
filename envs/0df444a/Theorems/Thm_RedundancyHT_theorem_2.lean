-- Prove2me | Theorems.Thm_RedundancyHT_theorem_2
-- name    : RedundancyHT.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:24.985194+00:00
-- url     : https://prove2.me/theorems/f15e3f20-3d4b-406a-bff7-89832bedc7d5
-- title:
--   Theorem 2, p.12: the scaled stationary job counts collapse onto one exponential variable, for both mechanisms
-- statement:
--   Consider $N$ parallel servers with speeds $\mu_1,\dots,\mu_N$ and job types $S\subseteq\{1,\dots,N\}$, arriving as independent Poisson processes of rates $N\lambda p_S$ and replicated to the servers in $S$. Under cancel-on-completion the other replicas are discarded when the first replica finishes. Under cancel-on-start they are discarded when the first replica starts, and an arriving job takes the longest idle compatible server. Let $\mathcal T^*$ be the unique maximizer of the capacity ratio $\rho_{\mathcal T}=p_{\mathcal T}/\mu_{\mathcal T}$ and $\lambda^*=\mu_{\mathcal T^*}/(Np_{\mathcal T^*})$.
--
--   For every $\lambda\in(0,\lambda^*)$ both systems have a stationary law, and for both mechanisms the stationary numbers of jobs of each type satisfy
--   $$\Bigl(1-\frac{\lambda}{\lambda^*}\Bigr)(Q_S)_{S\in\mathcal S}\xrightarrow{d}\Bigl(\mathrm{Exp}(1)\Bigl(\frac{p_S}{p_{\mathcal T^*}}\Bigr)_{S\in\mathcal T^*},(0)_{S\notin\mathcal T^*}\Bigr)$$
--   as $\lambda\uparrow\lambda^*$.
--
--   A single exponential variable drives all critical job types, and the assignment constraints enter only through $\mathcal T^*$. For $\mathcal T^*=\mathcal S$ and $\lambda^*=\mu$ this is the universality result of the paper, Theorem 1: the system behaves like a multi-class M/M/1 queue.
--
--   **Formalization Note** The convergence is stated for every family of stationary laws on $(0,\lambda^*)$, along $\lambda\uparrow\lambda^*$. The cancel-on-start count $Q_S$ includes jobs in service.
--
--   Differences from the source:
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - reading: the subset 𝒯* that maximizes the capacity ratio is unique, i.e., the vector of critical arrival rates can reach any point on the boundary except for its extreme vertices → IsCriticalSubset, the first sentence of Assumption 3; reason: the clause after i.e. is not equivalent: with N = 3, S_i = {i}, p_1/µ_1 = p_2/µ_2 > p_3/µ_3 the maximizer is not unique and the critical point is not a vertex
--   - reading: the stationary distribution, whose existence and uniqueness are taken for granted → every family of stationary laws on (0, λ*); reason: the laws exist (the goal proves it) and two servers compatible with no type make the c.o.s. law non-unique, so the universal statement covers the source's law in every case
--   - encoding: continuous-time Markov processes → uniformized EventChain with null events and its stationary laws; reason: uniformization does not change stationary laws, because the total clock rate is constant
--   - encoding: for c.o.s. the state descriptor (c;u) omits the jobs in service, so Q_S is not a function of it → laws of the published full QueueState and the count cosCount, which includes jobs in service; reason: Q_S counts jobs in service (p.9)
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Theorem 2, p.12

import Definitions.Def_RedundancyHT_IsCriticalSubset
import Definitions.Def_RedundancyHT_lamStar
import Definitions.Def_RedundancyHT_cocStationary
import Definitions.Def_RedundancyHT_load
import Definitions.Def_RedundancyHT_cosCount
import Definitions.Def_RedundancyHT_scaledLaw
import Definitions.Def_RedundancyHT_limitLaw
import Definitions.Def_RedundancyHT_ConvergesInLaw

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **Theorem 2** (arXiv:2005.14566v5, p.12). Let `𝒯*` be the critical subset of Definition 1 under
Assumption 3. For `λ ∈ (0, λ*)` both mechanisms have stationary laws, and for both the scaled
stationary job counts `(1 - λ/λ*) (Q_S)_{S∈𝒮}` converge in distribution, as `λ ↑ λ*`, to
`(Exp(1) (p_S/p_𝒯*)_{S∈𝒯*}, (0)_{S∉𝒯*})`.

**Formalization Note.**
1. `D : Model n m` gives the types, servers and rates: `p_S = pOf D S`, `µ_n = D.service n`, and the
   arrival rate `N λ p_S` is `load D lam * D.nominal S`. `hne` says that types are non-empty (p.4).
2. The c.o.c. state is the sequence of job types, and `Q_S` is `c.count S`. The c.o.s. queue is the
   published FCFS-ALIS `queueChain`, whose state keeps the jobs in service, and `Q_S` is `cosCount`.
3. The limits hold for every family of stationary laws, which is assumed on `(0, λ*)` only. For
   c.o.c. the law is unique (`equation_3`). For c.o.s. it need not be when two servers are compatible
   with no type, and the job counts have the same law on all closed classes.
4. The filter is `𝓝[<] λ*`, and `λ* > 0` makes it eventually inside `(0, λ*)`.
5. Neither `𝒯* = 𝒮` nor `λ* = µ` nor "every server is compatible with a type" is assumed. -/
theorem theorem_2 {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (T : Finset (Fin n)) (hT : IsCriticalSubset D T) :
    (∀ lam, 0 < lam → lam < lamStar D T →
      (∃ p, cocStationary D (load D lam) p) ∧ Stable D (load D lam)) ∧
    (∀ π : ℝ → List (Fin n) → ℝ≥0∞,
      (∀ lam, 0 < lam → lam < lamStar D T → cocStationary D (load D lam) (π lam)) →
      ConvergesInLaw
        (fun lam => scaledLaw (π lam) (fun c i => c.count i) (1 - lam / lamStar D T))
        (𝓝[<] lamStar D T) (limitLaw D T)) ∧
    (∀ π : ℝ → QueueState n m → ℝ≥0∞,
      (∀ lam, 0 < lam → lam < lamStar D T → stationary D (load D lam) (π lam)) →
      ConvergesInLaw
        (fun lam => scaledLaw (π lam) cosCount (1 - lam / lamStar D T))
        (𝓝[<] lamStar D T) (limitLaw D T)) := by sorry

end RedundancyHT
