-- Prove2me | Theorems.Thm_RoslingAssembly_finite_discounted_cost_policy
-- name    : RoslingAssembly.finite_discounted_cost_policy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:46:25.545056+00:00
-- url     : https://prove2.me/theorems/9b14548a-e1a9-47dc-8e0e-b59d03abf6e2
-- title:
--   A feasible policy of finite discounted cost exists ($\beta<1$)
-- statement:
--   Consider problem P for an assembly network with lead times $l$, arbitrary real costs $H$ and $p$, i.i.d. demands $\xi_t\ge0$ with a density and mean $\lambda\in(0,\infty)$, and a consistent pre-horizon history with $\xi_t\ge0$ for $t\le0$. Then there is a policy that is non-anticipating and measurable, satisfies constraint (3) along every demand path, and has finite discounted cost
--   $$\sum_{t\ge1}\beta^{t-1}\,\mathbb E|c_t|<\infty\qquad\text{for every }\beta\in(0,1).$$
--
--   The proof of Theorem 4(i) starts from such a policy ("suppose that a finite optimal policy exists") and perturbs it.
--
--   **Formalization Note** The order-nothing policy $Y_{it}=X_{it}$ is an example.
--
--   Differences from the source:
--   - reading: the proof supposes that a finite optimal policy exists → a feasible policy with finite cost exists; reason: the argument only uses that the base policy has finite cost, not that it is optimal
--   - reading: the positions Y and demands ξ of periods t ≤ 0, which (3) refers to, are not specified → given history `Yh`, `ξh` with ξ_t ≥ 0 that satisfies (3) on −max_i l_i ≤ t ≤ 0 (`HistOK`); reason: without it problem P can have no feasible policy (N = 2, l_1 = 0, l_2 = 1, Y_{1,0} = 5, Y_{2,0} = 0, ξ_0 = 0 force 5 ≤ Y_11 ≤ 0); a past state of the system obeys (3) (p. 566, X^l_it ≥ Y_kt if i ∈ P(k)); only a window is required
--   - generalization: the items are indexed so that M_i ≥ M_{i−1} for all i (p. 567) → not assumed; only the clause k < i for k ∈ A(i) is kept (`Network.s_lt`); reason: the clause is never used; every tree has such an indexing and the statement is invariant under reindexing, so the Lean statement specializes to the paper's
--   - encoding: items 1, …, N, end item 1, s(1) = 0, M_0 = 0 → items `Fin N`, 0-based, end item 0, `s 0 = none`, `Ms 0 = 0`; reason: renaming of indices; same instances
--   - encoding: decisions Y_it dependent on system history up to period t; objective E{Σ_t α^{t−1}(…)} → deterministic measurable functions of ξ_1, …, ξ_{t−1} on the canonical i.i.d. space, (3) on every demand path, objective Σ_t α^{t−1} E[c_t] for policies with Σ_t α^{t−1} E|c_t| < ∞ (`Admissible`); reason: restricting the policies that witness an existence claim only strengthens it; for such policies Σ_t E = E Σ_t (Fubini)
--   - encoding: ξ_t ≥ 0 i.i.d. with density φ and mean λ > 0; φ_1^{l_1+1} the (l_1 + 1)-fold convolution → law μ with μ(−∞, 0) = 0, μ ≪ Lebesgue, ∫|x| dμ < ∞, ∫ x dμ > 0, on (ℕ → ℝ, `Measure.infinitePi`); ∫_y^∞ (ξ − y) φ^{l_1+1}(ξ) dξ written as E[(ξ_1 + … + ξ_{l_1+1} − y)^+] under `Measure.pi`; reason: same objects
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, Appendix B, Proof of Theorem 4, p. 578 (unnumbered; presupposed by 'suppose that a finite optimal policy exists')

import Mathlib
import Definitions.Def_RoslingAssembly_IsPolicy
import Definitions.Def_RoslingAssembly_Feasible
import Definitions.Def_RoslingAssembly_HistOK
import Definitions.Def_RoslingAssembly_Admissible
open MeasureTheory

namespace RoslingAssembly

/-- **A feasible policy with finite discounted cost exists** (Appendix B, Proof of Theorem 4,
p. 578, unnumbered; presupposed). Rosling, *Optimal Inventory Policies for Assembly Systems under
Random Demands*, Operations Research 37(4), 1989, p. 578: "(i) Consider the subsystem {i} ∪ B(i)
and suppose that a finite optimal policy exists."

Under the standing assumptions of the model (an assembly tree with lead times, arbitrary real
costs `H`, `p`; i.i.d. demands with a density, `ξ ≥ 0`, finite mean `λ > 0`; a pre-horizon
history consistent with (3)), there is a policy that is non-anticipating and measurable,
satisfies constraint (3) on every demand path, and has finite discounted cost (2) for every
discount factor `β ∈ (0, 1)`.

**Formalization Note.** The order-nothing policy `Y_it = X_it` is such a policy. The paper only
supposes a finite (optimal) policy; this statement is the finiteness it needs, for every
`β < 1` at once. Items `Fin N` 0-based, periods in the paper's numbering. -/
theorem finite_discounted_cost_policy {N : ℕ} [NeZero N] (net : Network N) (ℓ : Fin N → ℕ)
    (H : Fin N → ℝ) (p : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμac : μ ≪ volume) (hμi : Integrable (fun x => x) μ)
    (hlam : 0 < ∫ x, x ∂μ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (hξh : ∀ t ≤ 0, 0 ≤ ξh t)
    (hHist : HistOK net ℓ Yh ξh) :
    ∃ pol : ℕ → (ℕ → ℝ) → Fin N → ℝ, IsPolicy pol ∧ Feasible net ℓ Yh ξh pol ∧
      ∀ β ∈ Set.Ioo (0 : ℝ) 1, Admissible net ℓ H p μ Yh pol β := by sorry

end RoslingAssembly
