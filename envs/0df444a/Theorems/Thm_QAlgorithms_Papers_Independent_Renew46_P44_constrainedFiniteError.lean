-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_constrainedFiniteError
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.constrainedFiniteError
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:36:13.431997+00:00
-- url     : https://prove2.me/theorems/5215e48d-1c93-41fb-bf03-7e3c39a8e62a
-- title:
--   §IV.3, (73)–(79): finite-block constrained pure-state error bounds
-- statement:
--   Let normalized pure signals have nonnegative cost $f$, let $\pi$ have expected cost at most a finite budget $E$, and choose integers $n,M\ge1$ with actual rate $R=\log M/n<C$. Set $0\le s\le1$, $t\ge1$, $p\ge0$, $\delta>0$, and
--
--   $$\nu=\Pr_{\pi^{\otimes n}}\{nE-\delta\le\textstyle\sum_kf(x_k)\le nE\}>0.$$
--
--   Assume the tilted mass $\int e^{p(f-E)}d\pi$ is finite. With
--
--   $$\mu(s,p)=-\log\operatorname{Tr}\left(\int e^{p(f(x)-E)}|\psi_x\rangle\langle\psi_x|\,\pi(dx)\right)^{1+s},$$
--
--   $$\widetilde\mu(t,p)=-t\log\iint e^{p(f(x)+f(y)-2E)}|\langle\psi_x,\psi_y\rangle|^{2/t}\,\pi(dx)\pi(dy),$$
--
--   one has
--
--   $$p(n,M)\le2\left(\frac{e^{p\delta}}\nu\right)^2 e^{-n[\mu(s,p)-sR]},$$
--
--   $$p(n,M)\le\exp\left(-n\left[\widetilde\mu(t,p)-t\left(R+\frac2n\log\frac{2e^{p\delta}}\nu\right)\right]\right).$$
--
--   For discrete alphabets the integrals are sums. For continuous alphabets use a Borel subset of finite-dimensional Euclidean space, a weakly continuous projector family, lower-semicontinuous $f$, and Borel probability $\pi$. These are finite-block bounds; no general asymptotic lower bound on $\sqrt n\nu$ is claimed.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 22, §IV.3, (73)–(79): finite-block constrained pure-state error bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.22-23, (73)-(79): discrete AND continuous finite-block bounds.
Tilted finiteness and positive shell probability state the conditioning domain;
they do not assume the false general shell asymptotic used later in (80)-(81).
For integer M use its actual rate log(M)/n, exactly equivalent to M=exp(nR). -/
theorem constrainedFiniteError :
    (∀ {A I : Type} [Nonempty A] [Nonempty I]
      (psi : A → Hilbert I), (∀ a, ‖psi a‖ = 1) →
      ∀ (pi : DiscreteInputLaw A) (f : A → ℝ) (E s t p delta : ℝ) (n M : ℕ),
      (∀ a, 0 ≤ f a) → HasMeanCostBound f E pi →
      0 < n → 0 < M → 0 ≤ s → s ≤ 1 → 1 ≤ t → 0 ≤ p → 0 < delta →
      Summable (fun a => pi.weight a * Real.exp (p * (f a - E))) →
      0 < shellProbability pi f E delta n →
      ENNReal.ofReal (Real.log (M : ℝ) / (n : ℝ)) <
        averageErrorCqCapacity (fun a => TC.rankOne (psi a)) f E →
      cqError (fun a => TC.rankOne (psi a)) f E n M ≤
        ENNReal.ofReal (finiteRandomBound n M (tiltedMu psi pi f E s p) s p delta
          (shellProbability pi f E delta n)) ∧
      cqError (fun a => TC.rankOne (psi a)) f E n M ≤
        ENNReal.ofReal (finiteExpurgatedBound n M (tiltedExpurgatedMu psi pi f E t p)
          t p delta (shellProbability pi f E delta n))) ∧
    (∀ (d : ℕ) (A : Set (EuclideanSpace ℝ (Fin d))), MeasurableSet A →
      ∀ {I : Type} [Nonempty I] (psi : A → Hilbert I), (∀ a, ‖psi a‖ = 1) →
      (∀ i j, Continuous (fun a => TC.rankOne (psi a) i j)) →
      ∀ (pi : Measure A) (f : A → ℝ) (E s t p delta : ℝ) (n M : ℕ),
      (∀ a, 0 ≤ f a) → LowerSemicontinuous f → AdmissibleMeasure f E pi →
      0 < n → 0 < M → 0 ≤ s → s ≤ 1 → 1 ≤ t → 0 ≤ p → 0 < delta →
      Integrable (fun a => Real.exp (p * (f a - E))) pi →
      0 < integralShell pi f E delta n →
      ENNReal.ofReal (Real.log (M : ℝ) / (n : ℝ)) <
        averageErrorCqCapacity (fun a => TC.rankOne (psi a)) f E →
      cqError (fun a => TC.rankOne (psi a)) f E n M ≤
        ENNReal.ofReal (finiteRandomBound n M (integralTiltMu psi pi f E s p) s p delta
          (integralShell pi f E delta n)) ∧
      cqError (fun a => TC.rankOne (psi a)) f E n M ≤
        ENNReal.ofReal (finiteExpurgatedBound n M (integralExpurgatedMu psi pi f E t p)
          t p delta (integralShell pi f E delta n))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
