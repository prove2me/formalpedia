-- Prove2me | Theorems.Thm_PandoraComb_proposition_4_1
-- name    : PandoraComb.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:32.146035+00:00
-- url     : https://prove2.me/theorems/9dd75311-0551-45ff-9503-1b267c0059aa
-- title:
--   Proposition 4.1 — the discretization $T^\epsilon$ loses at most $2\epsilon$, and fixed order strategies transfer back
-- statement:
--   Let $\mathcal I=(D_1,\dots,D_n,c)$ be an instance (independent non-negative values with finite expectations; $c$ normalized and monotone), let $\epsilon>0$ and let $\mathcal I^\epsilon=T^\epsilon(\mathcal I)$, whose laws are those of $\epsilon\lfloor\min(V_i,\kappa_\epsilon)/\epsilon\rfloor$ and whose cost is $c$. Then:
--
--   1. for every admissible strategy $\pi$ on $\mathcal I$ there is an admissible strategy $\pi'$ on $\mathcal I^\epsilon$ with
--   $$u(\mathcal I;\pi)\le u(\mathcal I^\epsilon;\pi')+2\epsilon;$$
--   2. for every admissible strategy $\pi'$ on $\mathcal I^\epsilon$ there is an admissible strategy $\pi$ on $\mathcal I$ with $u(\mathcal I;\pi)\ge u(\mathcal I^\epsilon;\pi')$; furthermore, if $\pi'$ is a fixed order strategy, then $\pi$ can be taken fixed order.
--
--   The proposition reduces Theorem 4.1 to instances with finitely supported laws.
--
--   Differences from the source:
--   - encoding: κ_ϵ := min{κ ≥ 0 | Σ E[(V_i − κ)^+] ≤ ϵ} → kappa D ε, the infimum of the same set; reason: the set is nonempty, bounded below and closed, so the infimum is the minimum
--   - encoding: "if π′ is a fixed-order strategy, then there exists such a fixed-order strategy π" → one π with the inequality such that (∃ σ, IsFixedOrder σ π′) → ∃ σ, IsFixedOrder σ π; reason: equivalent to the two-sentence form
--   - encoding: Π, all (randomized) strategies, deciding from the sequence of opened boxes and realized values so far, with coins tossed a priori (p.7) → admissible strategies: decisions read the ordered history and one uniform seed s ∈ [0,1] independent of the values, and are measurable in the observed values and the seed; reason: one uniform seed generates any finite family of coin tosses; measurability is what makes E[V(π)] and E[c(S(π))] defined, and it holds for every strategy the paper uses
--   - encoding: V(π) = max over S(π) of V_i, u(π) = E[V(π)] − E[c(S(π))] (p.7) → reward max(0, max observed value), utility = expectation of reward minus c(set of opened boxes); reason: values are non-negative a.s. and the empty strategy has utility 0 (pp.8, 24), so the two rewards agree a.s.
--   - encoding: boxes [n], c : 2^[n] → ℝ≥0 normalized and monotone (p.7) → boxes a finite type ι, c : Finset ι → ℝ with c ∅ = 0 and Monotone c; reason: relabeling [n] as ι changes no instance; c ≥ 0 follows from c ∅ = 0 and monotonicity
--   - encoding: a strategy chooses an uninspected box or halts (p.7) → a request for an already opened box halts the run; at most |ι| rounds; reason: a legal strategy never makes such a request, and |ι| rounds suffice to open every box
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, Proposition 4.1, p.18 (Transformation 1, p.18; proof pp.18–19)

import Definitions.Def_PandoraComb_Model
import Definitions.Def_PandoraComb_FixedOrder
import Definitions.Def_PandoraComb_Discretize

open MeasureTheory

namespace PandoraComb

/-- **Proposition 4.1** (arXiv:2303.01078v1, p.18): "For every instance I and every ϵ > 0, let
I^ϵ = T^ϵ(I). Then the following properties hold:
1. For every strategy π on instance I there exists a strategy π′ on instance I^ϵ such that
u(I;π) ≤ u(I^ϵ;π′) + 2ϵ.
2. For every strategy π′ on instance I^ϵ there exists a strategy π on instance I such that
u(I;π) ≥ u(I^ϵ;π′). Furthermore, if π′ is a fixed-order strategy, then there exists such a
fixed-order strategy π."

**Formalization Note.** `I^ϵ = (discretize D ε, c)` (Transformation 1, p.18). Strategies on both
instances are the admissible (randomized, adaptive) strategies. -/
theorem proposition_4_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → Measure ℝ)
    (c : Finset ι → ℝ) (hI : IsInstance D c) (ε : ℝ) (hε : 0 < ε) :
    (∀ π : Strategy ι, Admissible π →
      ∃ π' : Strategy ι, Admissible π' ∧ utility D c π ≤ utility (discretize D ε) c π' + 2 * ε) ∧
    (∀ π' : Strategy ι, Admissible π' →
      ∃ π : Strategy ι, Admissible π ∧ utility (discretize D ε) c π' ≤ utility D c π ∧
        ((∃ σ, IsFixedOrder σ π') → ∃ σ, IsFixedOrder σ π)) := by sorry

end PandoraComb
