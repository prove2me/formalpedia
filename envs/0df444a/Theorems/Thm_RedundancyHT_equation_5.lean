-- Prove2me | Theorems.Thm_RedundancyHT_equation_5
-- name    : RedundancyHT.equation_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:03.234859+00:00
-- url     : https://prove2.me/theorems/daf5686d-3d2a-490d-a09a-8771d85c2880
-- title:
--   (5), p.8: the stationary distribution of the c.o.s. descriptor $(c;u)$
-- statement:
--   Let $\lambda>0$ satisfy the stability conditions. Under every stationary law of the cancel-on-start queue with assignment to the longest idle server, the descriptor $(c_1,\dots,c_{\tilde M};u_1,\dots,u_L)$ has the distribution
--   $$\pi_{\mathrm{c.o.s.}}(c,u)=C'\prod_{i=1}^{\tilde M}\frac{N\lambda p_{c_i}}{\mu(c_1,\dots,c_i)}\prod_{l=1}^{L}\frac{\mu_{u_l}}{\lambda_{\mathcal C(u_1,\dots,u_l)}},$$
--   with a constant $C'>0$, on the pairs in which $u$ lists distinct useful servers and no job in $c$ is compatible with a server in $u$. All other pairs have probability zero.
--
--   The paper cites this product form. Its theorem for cancel-on-start is derived from it.
--
--   Differences from the source:
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - reading: u runs over the idle servers, with division by λ_𝒞(u_1,…,u_l) → u lists the useful idle servers only (idle.filter useful); reason: with every server useful this is the printed list; a server compatible with no type would give λ_𝒞 = 0, and it has no effect on the system
--   - encoding: the stability conditions (1) and (2) → StabilityOne, i.e. (1); reason: (1) and (2) are equivalent, which is equations_1_2
--   - reading: π_c.o.s.(c1, . . . , cM; u1, . . . , uL) with M printed on one side and M̃ on the other → c has length M̃; reason: c lists the waiting jobs, so the M on the page is a slip for M̃
--   - reading: the stationary distribution, whose existence and uniqueness are taken for granted → every stationary law at the given λ; reason: the laws exist (the goal proves it) and two servers compatible with no type make the c.o.s. law non-unique, so the universal statement covers the source's law in every case
--   - encoding: continuous-time Markov processes → uniformized EventChain with null events and its stationary laws; reason: uniformization does not change stationary laws, because the total clock rate is constant
--   - encoding: for c.o.s. the state descriptor (c;u) omits the jobs in service, so Q_S is not a function of it → laws of the published full QueueState, pushed forward by descr to the pair (c;u); reason: (5) is the law of the descriptor, and descrLaw reads it off any law of the full state
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, display (5), p.8 (the paper cites [27])

import Definitions.Def_RedundancyHT_StabilityOne
import Definitions.Def_RedundancyHT_load
import Definitions.Def_RedundancyHT_descrLaw
import Definitions.Def_RedundancyHT_ValidDescr
import Definitions.Def_RedundancyHT_cocWeight
import Definitions.Def_RedundancyHT_idleWeight

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay Classical
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The stationary distribution (5) of `(c;u)`**, from Gardner and Righter
(arXiv:2005.14566v5, p.8): under the stability conditions, for every stationary law of the full
c.o.s. queue, the law of the descriptor vanishes off the valid pairs and on them equals
`C′ ∏_{i} N λ p_{c_i}/µ(c₁,…,c_i) ∏_{l} µ_{u_l}/λ_{𝒞(u₁,…,u_l)}`.

**Formalization Note.** `C′` is the mass of `([], [])`, whose weight is the empty product. The list
`u` holds the useful idle servers (see `descr`), so every `λ_𝒞` here is positive. `u₁` is the longest
idle server. The queue is the published FCFS-ALIS queue, which is assignment rule (iii) of p.8: a
new job takes the first compatible server of the idle list, longest idle first, and a free server
takes the oldest compatible waiting job. -/
theorem equation_5 {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (lam : ℝ) (hlam : 0 < lam) (h : StabilityOne D lam)
    (p : QueueState n m → ℝ≥0∞) (hp : stationary D (load D lam) p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : List (Fin n)) (u : List (Fin m)),
      descrLaw D p (c, u) =
        if ValidDescr D c u then
          ENNReal.ofReal (C * (cocWeight D lam c * idleWeight D lam u))
        else 0 := by sorry

end RedundancyHT
