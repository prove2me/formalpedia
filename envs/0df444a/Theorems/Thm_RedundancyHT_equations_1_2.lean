-- Prove2me | Theorems.Thm_RedundancyHT_equations_1_2
-- name    : RedundancyHT.equations_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:42.65697+00:00
-- url     : https://prove2.me/theorems/10ca7f5b-ca57-40ce-bfc8-79445c198fa7
-- title:
--   (1), (2), p.5, and p.9: the stability conditions are equivalent, and equivalent to $\lambda<\lambda^*$
-- statement:
--   Let $\mathcal T^*$ be a maximizer of the capacity ratio and $\lambda>0$. Then the conditions
--   $$N\lambda\sum_{S\in\mathcal T}p_S<\sum_{n\in\bigcup_{S\in\mathcal T}S}\mu_n\quad\text{for all non-empty }\mathcal T\subseteq\mathcal S\tag{1}$$
--   and
--   $$N\lambda\sum_{S:\,S\subseteq U}p_S<\sum_{n\in U}\mu_n\quad\text{for all non-empty }U\subseteq\{1,\dots,N\}\tag{2}$$
--   are equivalent, and each is equivalent to $\lambda<\lambda^*$.
--
--   This identifies the stability region of the system with an interval of the normalized arrival rate, which is what gives the limit $\lambda\uparrow\lambda^*$ its meaning.
--
--   Differences from the source:
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - generalization: 𝒯* is the critical subset of Definition 1 → any maximizer of the capacity ratio; reason: the critical subset is a maximizer
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Assumption 1, displays (1), (2), p.5, and the note below Definition 1, p.9

import Definitions.Def_RedundancyHT_IsCapacityMaximizer
import Definitions.Def_RedundancyHT_StabilityOne
import Definitions.Def_RedundancyHT_StabilityTwo
import Definitions.Def_RedundancyHT_lamStar

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **(1) ⇔ (2) ⇔ λ < λ*** (arXiv:2005.14566v5, Assumption 1, p.5, and the note below Definition 1,
p.9).

**Formalization Note.** Any maximizer of the capacity ratio serves, so uniqueness is not assumed.
`hne` says that job types are non-empty server sets (p.4). -/
theorem equations_1_2 {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (T : Finset (Fin n)) (hT : IsCapacityMaximizer D T) (lam : ℝ) (hlam : 0 < lam) :
    (StabilityOne D lam ↔ StabilityTwo D lam) ∧ (StabilityOne D lam ↔ lam < lamStar D T) := by sorry

end RedundancyHT
