-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_proposition_C_3
-- name    : SRAudit.TwoPhase.Supplement.proposition_C_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T07:30:23.813428+00:00
-- url     : https://prove2.me/theorems/7a07459f-6e0b-4c65-886f-2768f142cbfe
-- title:
--   Proposition C.3, OA-5 — strict concavity of tier-2 profits, existence and uniqueness of the tier-2 equilibrium for every capacity, and the derivatives (C.12)–(C.13)
-- statement:
--   Let $g$ be a well-formed network, $\beta>0$, $\alpha\ge v_T$, and let $\pi_j$ be the payoff of tier-2 supplier $j$ in the game $P_2$ after substituting (13) and the inverse demand $p^*_{(2)}$.
--
--   1. **(a)** For every $j\in S(2)$ and every profile of the other suppliers, $\pi_j$ is strictly concave in $j$'s own strategy $s_j=(s_{j,i})_{i}$.
--   2. **(b)** For every capacity $M>0$ the game $P_2$ (strategies $0\le s_{j,i}\le M$) has a unique pure-strategy equilibrium.
--   3. **(c)** For $j\in S_i$, $i\in S(1)$,
--   $$\frac{\partial\pi_j}{\partial s_{j,i}}=-4\beta s_{j,i}+\Bigl(\alpha-v_T-4\beta\!\!\sum_{j'\in S_i\cup S_{ab}}\!\! s_{j',i}-2\beta\!\!\sum_{i'\in S(1)\setminus\{i\}}\sum_{j'\in S_{i'}\cup S_{ab}}\!\! s_{j',i'}\Bigr),\qquad\text{(C.12)}$$
--   and for $j\in S_{ab}$, $i\in S(1)$, the same expression minus $2\beta\sum_{i'\in S(1)\setminus\{i\}}s_{j,i'}$ (C.13).
--
--   Together with Propositions C.1 and C.2 this proves Theorem 1.
--
--   **Formalization Note** Strict concavity is on the coordinates of $j$'s supply links. The derivative in (c) is the derivative of $t\mapsto\pi_j$ with $s_{j,i}$ replaced by $t$, at $t=s_{j,i}$, for an arbitrary profile.
--
--   Differences from the source:
--   - reading: networks g ∈ G → networks satisfying WellFormedNet; reason: the published Network type admits tuples outside G (an absent firm with suppliers, shared suppliers with one firm); G is the set of networks of (C.36)
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-5–OA-6, Proposition C.3, (C.12), (C.13)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem proposition_C_3 {ι : Type} [DecidableEq ι] (E : Demand) (hE : E.Standing) :
    -- (a) strict concavity of `πj` in supplier `j`'s own strategy `sj`
    (∀ (g : Network ι), WellFormedNet g → ∀ j ∈ g.S2, ∀ s : ι → Firm → ℝ,
      StrictConcaveOn ℝ {y : Firm → ℝ | ∀ i, ¬ (i ∈ g.T1 ∧ j ∈ g.excl i ∪ g.Sab) → y i = 0}
        (fun y => tier2Payoff E g (Function.update s j y) j)) ∧
    -- (b) existence and uniqueness of the equilibrium of `P2`, for every capacity `M > 0`
    (∀ (M : ℝ), 0 < M → ∀ g : Network ι, WellFormedNet g → ∃! s : ι → Firm → ℝ, IsTier2Eq E g M s) ∧
    -- (c) the partial derivatives (C.12) and (C.13)
    (∀ (g : Network ι), WellFormedNet g → ∀ s : ι → Firm → ℝ, ∀ i ∈ g.T1,
      (∀ j ∈ g.excl i,
        HasDerivAt (fun t => tier2Payoff E g (Function.update s j (Function.update (s j) i t)) j)
          (-4 * E.β * s j i +
            (E.α - E.vT - 4 * E.β * ∑ j' ∈ g.excl i ∪ g.Sab, s j' i -
              2 * E.β * ∑ i' ∈ g.T1.erase i, ∑ j' ∈ g.excl i' ∪ g.Sab, s j' i'))
          (s j i)) ∧
      (∀ j ∈ g.Sab,
        HasDerivAt (fun t => tier2Payoff E g (Function.update s j (Function.update (s j) i t)) j)
          (-4 * E.β * s j i +
            (E.α - E.vT - 4 * E.β * ∑ j' ∈ g.excl i ∪ g.Sab, s j' i -
              2 * E.β * ∑ i' ∈ g.T1.erase i, ∑ j' ∈ g.excl i' ∪ g.Sab, s j' i') -
            2 * E.β * ∑ i' ∈ g.T1.erase i, s j i')
          (s j i))) := by sorry

end SRAudit.TwoPhase.Supplement
