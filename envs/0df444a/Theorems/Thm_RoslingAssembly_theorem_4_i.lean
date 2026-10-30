-- Prove2me | Theorems.Thm_RoslingAssembly_theorem_4_i
-- name    : RoslingAssembly.theorem_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T04:01:56.487014+00:00
-- url     : https://prove2.me/theorems/5f57e143-04c4-4f87-a670-aff45edb82e4
-- title:
--   Theorem 4(i): a negative discounted echelon cost of an item and its predecessors makes the minimal cost of problem P unbounded below
-- statement:
--   Consider problem P: an assembly system whose $N$ items form a tree rooted in the end item, with lead times $l_i\ge0$, arbitrary real installation holding costs $H_i$ (echelon costs $h_i=H_i-\sum_{k\in P(i)}H_k$) and backlog cost $p$, a discount factor $0<\alpha\le1$, i.i.d. demands $\xi_t\ge0$ for the end item with a density and mean $\lambda\in(0,\infty)$, a consistent pre-horizon history, ordering decisions $Y_{it}$ that depend on the demand history, constraint (3), and the objective (2) with constant (4) (its average-cost analogue when $\alpha=1$). If for some item $i$
--   $$h_i\,\alpha^{-M_{s(i)}}+\sum_{k\in B(i)}h_k\,\alpha^{-M_{s(k)}}<0,$$
--   then the minimal cost of problem P is unbounded below: for every real $K$ there is a non-anticipating measurable policy, satisfying (3) along every demand path, whose cost is a well-defined real number less than $K$, namely
--   1. its discounted cost $J_\alpha$ if $\alpha<1$;
--   2. its average cost $\lim_{\beta\to1^-}\frac{1-\beta}{\beta}J_\beta$ if $\alpha=1$.
--
--   The condition is the failure of part (i) of the Generalized Assumption: an item whose own and predecessors' echelon holding costs, discounted by the total lead times, sum to a negative number is worth stockpiling without limit.
--
--   **Formalization Note** Items are `Fin N`, 0-based (end item $0$); periods are integers with the paper's numbering.
--
--   Differences from the source:
--   - reading: the positions Y and demands ξ of periods t ≤ 0, which (3) refers to, are not specified → given history `Yh`, `ξh` with ξ_t ≥ 0 that satisfies (3) on −max_i l_i ≤ t ≤ 0 (`HistOK`); reason: without it problem P can have no feasible policy (N = 2, l_1 = 0, l_2 = 1, Y_{1,0} = 5, Y_{2,0} = 0, ξ_0 = 0 force 5 ≤ Y_11 ≤ 0); a past state of the system obeys (3) (p. 566, X^l_it ≥ Y_kt if i ∈ P(k)); only a window is required
--   - reading: α = 1: the average cost is (2) multiplied by (1 − α)/α, whereafter α → 1 (p. 567) → the policy has finite discounted cost J_β for every β ∈ (0, 1) and lim_{β→1⁻} ((1 − β)/β) J_β exists; reason: for a fixed policy the limit need not exist; requiring it is the strongest reading (it implies the liminf and limsup readings)
--   - generalization: the items are indexed so that M_i ≥ M_{i−1} for all i (p. 567) → not assumed; only the clause k < i for k ∈ A(i) is kept (`Network.s_lt`); reason: the clause is never used; every tree has such an indexing and the statement is invariant under reindexing, so the Lean statement specializes to the paper's
--   - encoding: items 1, …, N, end item 1, s(1) = 0, M_0 = 0 → items `Fin N`, 0-based, end item 0, `s 0 = none`, `Ms 0 = 0`; reason: renaming of indices; same instances
--   - encoding: decisions Y_it dependent on system history up to period t; objective E{Σ_t α^{t−1}(…)} → deterministic measurable functions of ξ_1, …, ξ_{t−1} on the canonical i.i.d. space, (3) on every demand path, objective Σ_t α^{t−1} E[c_t] for policies with Σ_t α^{t−1} E|c_t| < ∞ (`Admissible`); reason: restricting the policies that witness an existence claim only strengthens it; for such policies Σ_t E = E Σ_t (Fubini)
--   - encoding: ξ_t ≥ 0 i.i.d. with density φ and mean λ > 0; φ_1^{l_1+1} the (l_1 + 1)-fold convolution → law μ with μ(−∞, 0) = 0, μ ≪ Lebesgue, ∫|x| dμ < ∞, ∫ x dμ > 0, on (ℕ → ℝ, `Measure.infinitePi`); ∫_y^∞ (ξ − y) φ^{l_1+1}(ξ) dξ written as E[(ξ_1 + … + ξ_{l_1+1} − y)^+] under `Measure.pi`; reason: same objects
--   - encoding: the minimal cost of problem P is unbounded below → for every real K some policy that is feasible and has finite cost has cost < K; reason: the same as inf = −∞ over finite-cost policies; the witnesses have finite, well-defined cost, so this is the stronger form
--   - encoding: α^{−M} → integer power `α ^ (-(M : ℤ))` (zpow); reason: Lean convention; same values for α > 0
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §4, p. 574, Theorem 4(i); problem P, pp. 566–567; proof in Appendix B, p. 578

import Mathlib
import Definitions.Def_RoslingAssembly_IsPolicy
import Definitions.Def_RoslingAssembly_Feasible
import Definitions.Def_RoslingAssembly_HistOK
import Definitions.Def_RoslingAssembly_CostBelow
import Definitions.Def_RoslingAssembly_Network_B
import Definitions.Def_RoslingAssembly_Network_Ms
open MeasureTheory

namespace RoslingAssembly

/-- **Theorem 4(i)** (Practical Necessity of the Generalized Assumption), p. 574. Rosling,
*Optimal Inventory Policies for Assembly Systems under Random Demands*, Operations Research
37(4), 1989, Theorem 4(i), p. 574: "(i) If h_i · α^{−M_{s(i)}} + Σ_{k∈B(i)} h_k · α^{−M_{s(k)}} < 0
for some i, then the minimal cost of problem P is unbounded below."

Consider problem P (p. 567) for an assembly tree with lead times `ℓ`, arbitrary real
installation holding costs `H` (echelon costs `h_i = H_i − Σ_{k∈P(i)} H_k`) and backlog cost `p`,
a discount factor `0 < α ≤ 1`, i.i.d. demands with law `μ` (a density, `ξ ≥ 0`, finite mean
`λ > 0`) and a pre-horizon history consistent with (3). If
`h_i α^{−M_{s(i)}} + Σ_{k∈B(i)} h_k α^{−M_{s(k)}} < 0` for some item `i`, then for every real `K`
there is a non-anticipating measurable policy, satisfying (3) on every demand path, whose cost
in problem P is a well-defined real number below `K`: its discounted cost (2) + (4) if `α < 1`,
its average cost `lim_{β→1⁻} ((1 − β)/β) J_β` if `α = 1`.

**Formalization Note.** "The minimal cost is unbounded below" is stated as: for every `K` some
feasible policy of finite cost has cost `< K` (`CostBelow`). Items are `Fin N`, 0-based (end item
`0`); periods are integers with the paper's numbering, Lean decision index `t` being paper
period `t + 1`. `HistOK` and the average-cost limit are readings (see the natural-language
statement); the indexing clause `M_i ≥ M_{i−1}` is not assumed. -/
theorem theorem_4_i {N : ℕ} [NeZero N] (net : Network N) (ℓ : Fin N → ℕ) (H : Fin N → ℝ)
    (p : ℝ) (α : ℝ) (hα : 0 < α ∧ α ≤ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμac : μ ≪ volume) (hμi : Integrable (fun x => x) μ)
    (hlam : 0 < ∫ x, x ∂μ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (hξh : ∀ t ≤ 0, 0 ≤ ξh t)
    (hHist : HistOK net ℓ Yh ξh)
    (hcond : ∃ i : Fin N, net.h H i * α ^ (-(net.Ms ℓ i : ℤ)) +
      ∑ k ∈ net.B i, net.h H k * α ^ (-(net.Ms ℓ k : ℤ)) < 0) :
    ∀ K : ℝ, ∃ pol : ℕ → (ℕ → ℝ) → Fin N → ℝ, IsPolicy pol ∧ Feasible net ℓ Yh ξh pol ∧
      CostBelow net ℓ H p μ Yh α pol K := by sorry

end RoslingAssembly
