-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_favard_perturbation
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.favard_perturbation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:09:44.496381+00:00
-- url     : https://prove2.me/theorems/78a36f29-4e79-43a6-a1df-ce7523dc540a
-- title:
--   Lemma 5.1 (Perturbation of Favard spaces)
-- statement:
--   Let $A_0$ and $A=A_0+B$ on the common domain $D(A_0)$ generate strongly continuous contraction semigroups on a Banach space $X$. Suppose $a,b\ge0$ and $\|Bx\|\le a\|A_0x\|+b\|x\|$ on that domain. For $0<\alpha\le1$, write $M_{A,\alpha}(x)=\sup_{\lambda>0}\lambda^\alpha\|A(\lambda I-A)^{-1}x\|$. If $k\ge0$ and $M_{A_0,\alpha}(x)\le k$, then every $c>0$ satisfies
--
--   $$M_{A,\alpha}(x)\le\max\{2c^\alpha\|x\|,\ 3bc^{\alpha-1}\|x\|+(1+3a)k\}<\infty.$$
--
--   Moreover $F_\alpha(A_0)\subseteq F_\alpha(A)$, where $F_\alpha$ is defined by finiteness of $\sup_{t>0}\|T_tx-x\|/t^\alpha$. The generators are actual right-derivative graphs and resolvents are Laplace integrals. This is a quantitative perturbation statement for Favard spaces.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 22, Lemma 5.1 (Perturbation of Favard spaces)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P46

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P46

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Bridge50.P23 (energyMagnitude numberEnergy)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize rankOne tensorApply productCoeff IsBarycenter)

attribute [local instance] Classical.propDecidable Classical.decEq

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Lemma 5.1, PDF pp.22--23: common generator domain, relative A0 bound,
explicit resolvent bound for every c>0, and inclusion of the actual Favard spaces.
The perturbation's values outside the common domain have no role. -/
theorem favard_perturbation {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (T0 T : BanachContractionSemigroup X) (B : X → X)
    (a b alpha : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hsum : ∀ x y, GeneratorGraph T0 x y ↔ GeneratorGraph T x (y + B x))
    (hrel : ∀ x y, GeneratorGraph T0 x y → ‖B x‖ ≤ a * ‖y‖ + b * ‖x‖) :
    (∀ (x : X) (k : ℝ), 0 ≤ k → resolventSeminorm T0 alpha x ≤ ENNReal.ofReal k →
      ∀ c : ℝ, 0 < c → resolventSeminorm T alpha x ≤
        ENNReal.ofReal (max (2 * c ^ alpha * ‖x‖)
          (3 * b * c ^ (alpha - 1) * ‖x‖ + (1 + 3 * a) * k))) ∧
    favardSpace T0 alpha ⊆ favardSpace T alpha := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
