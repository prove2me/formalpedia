-- Prove2me | Theorems.Thm_RedundancyHT_theorem_2_coc
-- name    : RedundancyHT.theorem_2_coc
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:36.828986+00:00
-- url     : https://prove2.me/theorems/86eb8bda-8bc6-49e0-9998-1bdd4f152a62
-- title:
--   Theorem 2, p.12 (the c.o.c. half; the goal is Theorem 2 for both mechanisms)
-- statement:
--   Let $\mathcal T^*$ be the critical subset. For the cancel-on-completion mechanism,
--   $$\Bigl(1-\frac{\lambda}{\lambda^*}\Bigr)(Q_S)_{S\in\mathcal S}\xrightarrow{d}\Bigl(\mathrm{Exp}(1)\Bigl(\frac{p_S}{p_{\mathcal T^*}}\Bigr)_{S\in\mathcal T^*},(0)_{S\notin\mathcal T^*}\Bigr)$$
--   as $\lambda\uparrow\lambda^*$.
--
--   This is one half of the goal theorem, which states the same limit for both mechanisms.
--
--   Differences from the source:
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - reading: the subset 𝒯* that maximizes the capacity ratio is unique, i.e., the vector of critical arrival rates can reach any point on the boundary except for its extreme vertices → IsCriticalSubset, the first sentence of Assumption 3; reason: the clause after i.e. is not equivalent: with N = 3, S_i = {i}, p_1/µ_1 = p_2/µ_2 > p_3/µ_3 the maximizer is not unique and the critical point is not a vertex
--   - reading: the stationary distribution of the c.o.c. system → every family of stationary laws on (0, λ*); reason: equation_3 shows that there is exactly one law at each λ
--   - encoding: continuous-time Markov processes → uniformized EventChain with null events and its stationary laws; reason: uniformization does not change stationary laws, because the total clock rate is constant
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Theorem 2, p.12, c.o.c. half; proof pp.18–19

import Definitions.Def_RedundancyHT_IsCriticalSubset
import Definitions.Def_RedundancyHT_lamStar
import Definitions.Def_RedundancyHT_cocStationary
import Definitions.Def_RedundancyHT_load
import Definitions.Def_RedundancyHT_scaledLaw
import Definitions.Def_RedundancyHT_limitLaw
import Definitions.Def_RedundancyHT_ConvergesInLaw

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **Theorem 2, the c.o.c. half** (arXiv:2005.14566v5, p.12, proved on pp.18–19). The goal
`theorem_2` is the theorem for both mechanisms. -/
theorem theorem_2_coc {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (T : Finset (Fin n)) (hT : IsCriticalSubset D T)
    (π : ℝ → List (Fin n) → ℝ≥0∞)
    (hπ : ∀ lam, 0 < lam → lam < lamStar D T → cocStationary D (load D lam) (π lam)) :
    ConvergesInLaw
      (fun lam => scaledLaw (π lam) (fun c i => c.count i) (1 - lam / lamStar D T))
      (𝓝[<] lamStar D T) (limitLaw D T) := by sorry

end RedundancyHT
