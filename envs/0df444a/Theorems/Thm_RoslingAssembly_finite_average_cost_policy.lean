-- Prove2me | Theorems.Thm_RoslingAssembly_finite_average_cost_policy
-- name    : RoslingAssembly.finite_average_cost_policy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:47:26.915339+00:00
-- url     : https://prove2.me/theorems/1a55aa8d-9a19-4a30-ac83-a4c89f1707ac
-- title:
--   A feasible policy of finite average cost exists, also after perturbation ($\alpha=1$)
-- statement:
--   Under the assumptions of problem P (as in the previous milestone), there is a non-anticipating measurable policy $\pi$, satisfying constraint (3) along every demand path, such that for every item $i$ and every $n\ge0$ the perturbed policy $\pi'$ (which orders $n$ more units of every $k\in\{i\}\cup B(i)$ in period $M_m-M_k+1$ and keeps them) has finite discounted cost at every $\beta\in(0,1)$, and its average cost
--   $$\lim_{\beta\to1^-}\frac{1-\beta}{\beta}\,J_\beta(\pi')$$
--   exists. The case $n=0$ is $\pi$ itself.
--
--   This is the finite-cost presupposition of the proof of Theorem 4(i) in the average-cost case $\alpha=1$.
--
--   **Formalization Note** The statement covers the whole perturbed family because the $\alpha=1$ case of Theorem 4(i) needs the average cost of each perturbed policy to exist.
--
--   Differences from the source:
--   - reading: the proof supposes that a finite optimal policy exists → a feasible policy with finite cost exists; reason: the argument only uses that the base policy has finite cost, not that it is optimal
--   - reading: the positions Y and demands ξ of periods t ≤ 0, which (3) refers to, are not specified → given history `Yh`, `ξh` with ξ_t ≥ 0 that satisfies (3) on −max_i l_i ≤ t ≤ 0 (`HistOK`); reason: without it problem P can have no feasible policy (N = 2, l_1 = 0, l_2 = 1, Y_{1,0} = 5, Y_{2,0} = 0, ξ_0 = 0 force 5 ≤ Y_11 ≤ 0); a past state of the system obeys (3) (p. 566, X^l_it ≥ Y_kt if i ∈ P(k)); only a window is required
--   - reading: α = 1: the average cost is (2) multiplied by (1 − α)/α, whereafter α → 1 (p. 567) → the policy has finite discounted cost J_β for every β ∈ (0, 1) and lim_{β→1⁻} ((1 − β)/β) J_β exists; reason: for a fixed policy the limit need not exist; requiring it is the strongest reading (it implies the liminf and limsup readings)
--   - generalization: the items are indexed so that M_i ≥ M_{i−1} for all i (p. 567) → not assumed; only the clause k < i for k ∈ A(i) is kept (`Network.s_lt`); reason: the clause is never used; every tree has such an indexing and the statement is invariant under reindexing, so the Lean statement specializes to the paper's
--   - encoding: items 1, …, N, end item 1, s(1) = 0, M_0 = 0 → items `Fin N`, 0-based, end item 0, `s 0 = none`, `Ms 0 = 0`; reason: renaming of indices; same instances
--   - encoding: decisions Y_it dependent on system history up to period t; objective E{Σ_t α^{t−1}(…)} → deterministic measurable functions of ξ_1, …, ξ_{t−1} on the canonical i.i.d. space, (3) on every demand path, objective Σ_t α^{t−1} E[c_t] for policies with Σ_t α^{t−1} E|c_t| < ∞ (`Admissible`); reason: restricting the policies that witness an existence claim only strengthens it; for such policies Σ_t E = E Σ_t (Fubini)
--   - encoding: ξ_t ≥ 0 i.i.d. with density φ and mean λ > 0; φ_1^{l_1+1} the (l_1 + 1)-fold convolution → law μ with μ(−∞, 0) = 0, μ ≪ Lebesgue, ∫|x| dμ < ∞, ∫ x dμ > 0, on (ℕ → ℝ, `Measure.infinitePi`); ∫_y^∞ (ξ − y) φ^{l_1+1}(ξ) dξ written as E[(ξ_1 + … + ξ_{l_1+1} − y)^+] under `Measure.pi`; reason: same objects
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, Appendix B, Proof of Theorem 4, p. 578 (unnumbered; presupposed), with the average cost of §1, p. 567

import Mathlib
import Definitions.Def_RoslingAssembly_IsPolicy
import Definitions.Def_RoslingAssembly_Feasible
import Definitions.Def_RoslingAssembly_HistOK
import Definitions.Def_RoslingAssembly_Admissible
import Definitions.Def_RoslingAssembly_discCost
import Definitions.Def_RoslingAssembly_perturb
open MeasureTheory Filter Topology

namespace RoslingAssembly

/-- **A feasible policy with finite average cost exists, also after perturbation** (Appendix B,
Proof of Theorem 4, p. 578, unnumbered; presupposed, α = 1). Rosling, *Optimal Inventory Policies
for Assembly Systems under Random Demands*, Operations Research 37(4), 1989, p. 578: "(i) Consider
the subsystem {i} ∪ B(i) and suppose that a finite optimal policy exists."; p. 567: "The average
cost is constructed by multiplying (2) with the discount rate (1 − α)/α whereafter α → 1."

Under the standing assumptions of the model, there is a non-anticipating, measurable policy
satisfying (3) on every demand path such that, for every item `i` and every `n ≥ 0`, the policy
perturbed by `n` extra units of `{i} ∪ B(i)` (`perturb`; `n = 0` is the policy itself) has
finite discounted cost at every `β ∈ (0, 1)` and a finite average cost
`lim_{β→1⁻} ((1 − β)/β) · J_β`.

**Formalization Note.** This is the α = 1 counterpart of the finite-cost presupposition of the
proof, stated for the whole perturbed family, which is what the α = 1 case of Theorem 4(i)
needs. Items `Fin N` 0-based, periods in the paper's numbering. -/
theorem finite_average_cost_policy {N : ℕ} [NeZero N] (net : Network N) (ℓ : Fin N → ℕ)
    (H : Fin N → ℝ) (p : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμac : μ ≪ volume) (hμi : Integrable (fun x => x) μ)
    (hlam : 0 < ∫ x, x ∂μ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (hξh : ∀ t ≤ 0, 0 ≤ ξh t)
    (hHist : HistOK net ℓ Yh ξh) :
    ∃ pol : ℕ → (ℕ → ℝ) → Fin N → ℝ, IsPolicy pol ∧ Feasible net ℓ Yh ξh pol ∧
      ∀ (i : Fin N) (n : ℝ), 0 ≤ n →
        (∀ β ∈ Set.Ioo (0 : ℝ) 1, Admissible net ℓ H p μ Yh (perturb net ℓ pol i n) β) ∧
          ∃ v : ℝ, Tendsto (fun β => (1 - β) / β * discCost net ℓ H p μ Yh (perturb net ℓ pol i n) β)
            (𝓝[<] 1) (𝓝 v) := by sorry

end RoslingAssembly
