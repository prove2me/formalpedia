-- Prove2me | Theorems.Thm_RoslingAssembly_backlog_nonneg_antitone
-- name    : RoslingAssembly.backlog_nonneg_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T04:00:30.800969+00:00
-- url     : https://prove2.me/theorems/4b79affe-bd52-4513-b131-ed9494e0e8e5
-- title:
--   The expected backlog function is nonnegative and nonincreasing
-- statement:
--   Let the one-period demand have a density, be nonnegative and have finite mean $\lambda>0$. For every $m\in\mathbb N$ the expected backlog function
--   $$G_m(y)=\int_y^\infty(\xi-y)\,\varphi^{m+1}(\xi)\,d\xi=\mathbb E\big[(\xi_1+\dots+\xi_{m+1}-y)^+\big]$$
--   satisfies $G_m(y)\ge0$ for every $y\in\mathbb R$ and is nonincreasing in $y$.
--
--   With the cost formula for the perturbed policy, this bounds the end item's backlog term independently of the number of extra units.
--
--   **Formalization Note** The paper uses $m=l_1$.
--
--   Differences from the source:
--   - encoding: the backlog integral with φ_1^{l_1+1}, the convolution over l_1 + 1 periods → backlogG μ m for any m : ℕ, an expectation under Measure.pi over Fin (m + 1); reason: m is a name for the arbitrary lead time l_1; the convolution integral is the expectation of the (m + 1)-fold sum
--   - encoding: ξ_t ≥ 0 i.i.d. with density φ and mean λ > 0; φ_1^{l_1+1} the (l_1 + 1)-fold convolution → law μ with μ(−∞, 0) = 0, μ ≪ Lebesgue, ∫|x| dμ < ∞, ∫ x dμ > 0, on (ℕ → ℝ, `Measure.infinitePi`); ∫_y^∞ (ξ − y) φ^{l_1+1}(ξ) dξ written as E[(ξ_1 + … + ξ_{l_1+1} − y)^+] under `Measure.pi`; reason: same objects
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 567, (2) (unnumbered)

import Mathlib
import Definitions.Def_RoslingAssembly_backlogG
open MeasureTheory

namespace RoslingAssembly

/-- **The expected backlog function is nonnegative and nonincreasing** (p. 567, (2),
unnumbered). Rosling, *Optimal Inventory Policies for Assembly Systems under Random Demands*,
Operations Research 37(4), 1989, p. 567: the backlog term "∫_{Y_1t}^∞ (ξ − Y_1t) φ_1^{l_1+1}(ξ) dξ"
of (2), "where φ_1^{l_1+1}(·) is the convolution of φ(·) over (l_1 + 1) periods."

For a one-period demand law `μ` (a probability measure with a density, supported on `[0, ∞)`,
with finite mean `λ > 0`) and every `m : ℕ`, the function
`G_m(y) = ∫_y^∞ (ξ − y) φ^{m+1}(ξ) dξ = E[(ξ_1 + … + ξ_{m+1} − y)^+]` satisfies `G_m(y) ≥ 0` for
all `y` and is nonincreasing in `y`.

**Formalization Note.** The paper uses `m = l_1`, the end item's lead time; the statement holds
for every `m`. The convolution is written with `Measure.pi` over `Fin (m + 1)`. -/
theorem backlog_nonneg_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμac : μ ≪ volume) (hμi : Integrable (fun x => x) μ)
    (hlam : 0 < ∫ x, x ∂μ) (m : ℕ) :
    (∀ y : ℝ, 0 ≤ backlogG μ m y) ∧ Antitone (backlogG μ m) := by sorry

end RoslingAssembly
