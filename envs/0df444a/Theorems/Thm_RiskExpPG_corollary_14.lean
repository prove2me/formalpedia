-- Prove2me | Theorems.Thm_RiskExpPG_corollary_14
-- name    : RiskExpPG.corollary_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:27.918998+00:00
-- url     : https://prove2.me/theorems/de305506-f354-40bb-b1ec-4acce9ca4155
-- title:
--   Corollary 14 — $\Lambda^{(M)}_\theta$ is well defined and $\Lambda^{(M)}_\theta\uparrow\Lambda_\theta$ uniformly
-- statement:
--   Let Assumptions 1 and 2 hold. For every $M>1$ and $\theta$, the equation $g^{(M)}(\theta,\Lambda)=1$ has a unique solution $\Lambda^{(M)}_\theta$. Moreover
--   $$\Lambda^{(M)}_\theta\uparrow\Lambda_\theta\quad\text{as }M\uparrow\infty,\text{ uniformly over }\theta\in\mathbb R^l:$$
--   $\Lambda^{(M)}_\theta$ is nondecreasing in $M$ and bounded above by $\Lambda_\theta$, and for every $\varepsilon>0$ there is $M_0>1$ such that $\Lambda_\theta-\Lambda^{(M)}_\theta<\varepsilon$ for all $M\ge M_0$ and all $\theta$.
--
--   This makes the smooth truncation a uniform approximation of the cost, and it is what shows that sequences satisfying Assumption 4 exist.
--
--   Differences from the source:
--   - reading: no assumptions named in the statement → Assumptions 1 and 2; reason: these are the hypotheses of Lemmas 12 and 13 (pp.37, 39), on which the proof rests; Assumption 3 is not used
--   - reading: bounded functions and bounded derivatives in Assumptions 2 and 3 → bounds uniform in θ, with no continuity of the second derivative; reason: Lemma 12's proof and Lemma 17 need uniform bounds; the page says twice differentiable, not C²
--   - encoding: expectations over the first return time τ_{x*} → sums over finite excursions, in ℝ≥0∞ or as a real sum with its summability asserted; reason: Assumption 1 makes τ_{x*} finite almost surely, so the values agree and +∞ stays representable
--   - encoding: Λ^(M)_θ denotes the unique solution of g^(M)(θ, Λ) = 1 → the spec of the total function truncCost, as an added first clause; reason: the page takes it as the definition (p.8) and proves it in Lemma 13's proof; the clause excludes a junk infimum
--   - reading: Λ^(M)_θ ↑ Λ_θ as M ↑ ∞ uniformly → monotone in M, bounded by Λ_θ, and uniform convergence with M₀ independent of θ; reason: this is the meaning of the arrow, and §5.2 says Λ^(M) is smaller than Λ_θ
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, Corollary 14, p.41; §5.2, p.8, "the unique solution of"; Lemma 13, p.39

import Mathlib
import Definitions.Def_RiskExpPG_Chain
import Definitions.Def_RiskExpPG_Model
open Filter Topology MeasureTheory
open scoped ENNReal

namespace RiskExpPG

/-- **Corollary 14** (arXiv:2202.04157v2, p.41), with the specification of `Λ^(M)_θ` (§5.2, p.8) as
its first clause. For `M > 1`, `truncCost M θ` is the unique solution of `g^(M)(θ, Λ) = 1`. It is
nondecreasing in `M`, bounded by `Λ_θ`, and converges to `Λ_θ` uniformly over `θ ∈ ℝ^l`. -/
theorem corollary_14 {X : Type*} [Fintype X] [DecidableEq X] {l : ℕ} (m : Model X l)
    (hm : m.IsValid) (h1 : m.Assumption1) (h2 : m.Assumption2) :
    (∀ M, 1 < M → ∀ θ, m.gTrunc M θ (m.truncCost M θ) = 1 ∧
      ∀ Λ, m.gTrunc M θ Λ = 1 → Λ = m.truncCost M θ) ∧
    (∀ M M', 1 < M → M ≤ M' → ∀ θ,
      m.truncCost M θ ≤ m.truncCost M' θ ∧ m.truncCost M' θ ≤ m.riskCost θ) ∧
    ∀ ε > 0, ∃ M₀ > 1, ∀ M ≥ M₀, ∀ θ, m.riskCost θ - m.truncCost M θ < ε := by sorry

end RiskExpPG
