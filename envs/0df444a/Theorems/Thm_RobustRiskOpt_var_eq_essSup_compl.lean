-- Prove2me | Theorems.Thm_RobustRiskOpt_var_eq_essSup_compl
-- name    : RobustRiskOpt.var_eq_essSup_compl
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:41:40.699777+00:00
-- url     : https://prove2.me/theorems/a933fd9c-33d3-4470-abb4-1819a0d621fc
-- title:
--   (A.2), p.29 — $\mathrm{VaR}_p$ as an essential supremum off a tail event
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $p\in(0,1)$, and let $X$ be an $n$-dimensional random vector with law $\mu_X$. A Borel set $A\subset\mathbb R^n$ is a **$p$-tail event** of a measurable $h:\mathbb R^n\to\mathbb R$ if $\mu_X(A)=1-p$ and $h(x)\ge h(x')$ for $\mu_X$-a.e. $x\in A$ and $x'\in A^c$.
--
--   If $A$ is a $p$-tail event of $h$, then
--
--   $$
--   \mathrm{VaR}_p(h(X))=\operatorname{ess\,sup}(h\,|\,A^c),
--   $$
--
--   the essential supremum with respect to $\mu_X$ of $h$ on $A^c$.
--
--   The identity says that $\mathrm{VaR}_p$ does not see the values of a position on a tail event. It is what allows an optimizer to be changed on $A$ at no cost.
--
--   **Formalization Note** The essential supremum is the real `essSup` of $h$ under the restriction of $\mu_X$ to $A^c$. It has no junk value here, since $\mu_X(A)>0$ and $\mu_X(A^c)>0$. The tail event is the published `IsPTailEvent`.
--
--   Differences from the source:
--   - generalization: (A.2) is stated for h = g_X, and the proof also applies it to ĝ → every measurable h; reason: g_X and ĝ are special cases
--   - generalization: the probability space (Ω, F, P) is atomless (§2.1, p.5) → no atomlessness hypothesis on Ω; reason: it follows from the density of X in Assumption G, so the printed setting is a special case
--   - encoding: ℝⁿ with the Euclidean norm, n a positive integer → EuclideanSpace ℝ (Fin n) with 0 < n; reason: same space and norm
-- source:
--   Embrechts–Schied–Wang, Robustness in the Optimization of Risk Measures, arXiv:1809.09268v3, 11 Feb 2021, proof of Theorem 1, (A.2) and the definition of a p-tail event, p.29

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting
import Definitions.Def_RobustRiskOpt_Admissible

open MeasureTheory

namespace RobustRiskOpt

open ESAxioms.Characterization

/-- (A.2), p.29, in the proof of Theorem 1 (Embrechts–Schied–Wang, arXiv:1809.09268v3): for a
`p`-tail event `A` of `h` under `μ_X`, `VaR_p(h(X)) = ess-sup(h | Aᶜ)`, the essential supremum
with respect to `μ_X` of `h` on `Aᶜ`.

**Formalization Note** The paper states this for `h = g_X` and uses it for `ĝ` as well; it holds
for every measurable `h`. The real `essSup` has no junk value here: `μ_X(Aᶜ) = p > 0` and
`μ_X(A) = 1 − p > 0`, so `h` is essentially bounded above on `Aᶜ` and the defining set is
bounded below. `IsPTailEvent` is the published `ESAxioms.Characterization.IsPTailEvent`. -/
theorem var_eq_essSup_compl {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (X : Ω → E n)
    (hX : Measurable X) (h : E n → ℝ) (hh : Measurable h) (A : Set (E n))
    (hA : IsPTailEvent (P.map X) p h A) :
    VaR P p (h ∘ X) = essSup h ((P.map X).restrict Aᶜ) := by sorry

end RobustRiskOpt
