-- Prove2me | Theorems.Thm_Soar_hindsight_dominates
-- name    : Soar.hindsight_dominates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-22T18:58:27.125416+00:00
-- url     : https://prove2.me/theorems/d2ace628-1729-44b3-894b-82cdb8d2e1ec
-- title:
--   The hindsight optimum dominates every assignment rule
-- statement:
--   **Standing conventions.** Throughout, $\mathcal X$ (demand weight vectors) and $\mathcal Y$ (supply feature vectors) are measurable spaces, $P$ and $Q$ are probability measures on them, and the match quality function $\varphi : \mathcal X \times \mathcal Y \to \mathbb R$ is jointly measurable and bounded, $|\varphi(x,y)| \le C$ for all $x, y$. Expectations over $n$ i.i.d. demand units and $n$ independent i.i.d. supply units are integrals against the product measure $P^{\otimes n} \otimes Q^{\otimes n}$ on $\mathcal X^n \times \mathcal Y^n$. The hindsight optimum value is
--   $$U^H_n = \frac{1}{n}\,\mathbb E\Bigl[\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\sigma(t)}\bigr)\Bigr],$$
--   with $S_n$ the symmetric group, and the limiting hindsight optimum is $U_\infty = \sup_{n \ge 1} U^H_n$.
--
--   Let $(\Omega, \mu)$ be any probability space of auxiliary randomness, and let $\tau$ be any measurable assignment rule which, given the realized demand tuple $x \in \mathcal X^n$, the realized supply tuple $y \in \mathcal Y^n$ and a point $\omega \in \Omega$, returns a permutation $\tau(x, y, \omega) \in S_n$ (demand $t$ is matched to supply $\tau(x,y,\omega)(t)$). Then
--   $$\frac{1}{n}\,\mathbb E_{(X,Y) \sim P^{\otimes n} \otimes Q^{\otimes n},\ \omega \sim \mu}\Bigl[\sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\tau(X,Y,\omega)(t)}\bigr)\Bigr] \le U^H_n .$$
--
--   **Role.** A dynamic matching policy $\pi = (\pi_t)$ in the paper's sense assigns supply to each arriving demand unit as a possibly randomized function of the history; its realized assignment is one such rule $\tau$, so the statement gives $U_n(\pi) \le U^H_n$ for every policy, the inequality Appendix A calls straightforward. It applies in particular to SOAR and to the hindsight-optimal algorithm itself, for which it is an equality.
--
--   **Formalization Note** The rule $\tau$ is allowed to depend on all of $x$ and $y$ (an anticipative rule), which is more general than the paper's non-anticipative policies; the inequality is pointwise, so the generality costs nothing. Randomization is modelled through the auxiliary probability space, which may be trivial. The measurability of $\tau$ into the discrete $\sigma$-algebra of $S_n$ and the boundedness of $\varphi$ make the integrand integrable; the case $n = 0$ reads $0 \le 0$.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 2 and Appendix A (the inequality $U^H_n \ge U_n(\pi)$)

import Mathlib
import Definitions.Def_SoarModel

open MeasureTheory
open scoped BigOperators

namespace Soar

theorem hindsight_dominates {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Ω] (P : Measure X) (Q : Measure Y) (μ : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure μ]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (n : ℕ) (τ : (Fin n → X) × (Fin n → Y) → Ω → Equiv.Perm (Fin n))
    (hτ : Measurable (Function.uncurry τ)) :
    (∫ q, ∑ t, φ (q.1.1 t) (q.1.2 (τ q.1 q.2 t)) ∂(SoarPairMeasure P Q n).prod μ) / n
      ≤ SoarHindsight P Q φ n := by
  sorry

end Soar
