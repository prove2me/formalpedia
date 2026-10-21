-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_continuousErrorBounds
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.continuousErrorBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:56:35.108864+00:00
-- url     : https://prove2.me/theorems/0e4fae7f-3ad9-4fe7-b070-385fb15e93d3
-- title:
--   §IV: continuous-alphabet extensions of both error bounds, (38)–(39)
-- statement:
--   Let $A$ be a Borel subset of a finite-dimensional Euclidean space, with a weakly continuous family of normalized pure density operators $S_x$ on a complex Hilbert space and a real cost $f$ that extends continuously to the ambient space. Assume an affordable input exists and the capacity $C$ is finite. Let $\pi$ be any admissible Borel probability law with defined finite expected cost at most $E$. For integers $n,M\ge1$ set $R=\log M/n<C$. Let $p\ge0$, $\delta>0$, and let $\nu_{n,\delta}>0$ be the product-law probability of the total-cost shell $[nE-\delta,nE]$. Define
--
--   $$\mu(\pi,s,p)=-\log\operatorname{Tr}\left(\int_Ae^{p(f(x)-E)}S_x\,\pi(dx)\right)^{1+s},$$
--   $$\widetilde\mu(\pi,s,p)=-s\log\iint_{A\times A}e^{p(f(x)+f(y)-2E)}[\operatorname{Tr}(S_xS_y)]^{1/s}\,\pi(dx)\pi(dy).$$
--
--   On the random side assume the weighted coefficient integrals realize a bounded positive operator whose $(1+s)$-power has finite positive trace. On the expurgated side assume the overlap integrand is integrable against $\pi\otimes\pi$ with positive integral. On these respective domains,
--
--   $$p(n,M)\le2(e^{p\delta}/\nu_{n,\delta})^2e^{-n(\mu-sR)}\quad(0\le s\le1),$$
--   $$p(n,M)\le e^{-n[\widetilde\mu-s(R+(2/n)\log(2e^{p\delta}/\nu_{n,\delta}))]}\quad(s\ge1).$$
--
--   The error uses collective measurements, uniform messages and the cost constraint on every word. No density for $\pi$ or measurable choice of vector phases is assumed.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 12, §IV: continuous-alphabet extensions of both error bounds, (38)–(39)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section IV, PDF p.12, (38)-(39): both finite-block extensions, for all
Borel priors including singular ones. The alphabet and continuity assumptions
are those of Section II. The actual operator-power or
overlap convergence domains and a positive shell guard the displayed expressions. Overlaps avoid any phase choice. -/
theorem continuousErrorBounds {I : Type} (d : ℕ)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
    (S : A → constrainedCqState I) (hcontinuous : WeaklyContinuous (fun a => (S a).val))
    (hpure : ∀ a, ∃ psi : Hilbert I, ‖psi‖ = 1 ∧
      (S a).val = InnerProductSpace.rankOne ℂ psi psi)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Continuous f) (E : ℝ)
    (hfeasible : ∃ a : A, f a ≤ E) (hfinite : constrainedCqCapacity S (fun a : A => f a.val) E < ⊤)
    (pi : Measure A) (hpi : MeasureAdmissible (fun a : A => f a.val) E pi)
    (n M : ℕ) (hn : 0 < n) (hM : 0 < M)
    (hR : ENNReal.ofReal (Real.log (M : ℝ) / (n : ℝ)) < constrainedCqCapacity S (fun a : A => f a.val) E)
    (p delta : ℝ) (hp : 0 ≤ p) (hd : 0 < delta)
    (hnu : 0 < constrainedCqShell pi (fun a : A => f a.val) E n delta) :
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      randomDomain (fun a => (S a).val) pi (fun a : A => f a.val) E s p →
      constrainedCqError S (fun a : A => f a.val) E n M ≤
      2 * (Real.exp (p * delta) / constrainedCqShell pi (fun a : A => f a.val) E n delta) ^ 2 *
        Real.exp (-(n : ℝ) * (mu (fun a => (S a).val) pi (fun a : A => f a.val) E s p -
          s * (Real.log (M : ℝ) / (n : ℝ))))) ∧
    (∀ s : ℝ, 1 ≤ s →
      expurgatedDomain (fun a => (S a).val) pi (fun a : A => f a.val) E s p →
      constrainedCqError S (fun a : A => f a.val) E n M ≤
      Real.exp (-(n : ℝ) * (muEx (fun a => (S a).val) pi (fun a : A => f a.val) E s p -
        s * (Real.log (M : ℝ) / (n : ℝ) + 2 / (n : ℝ) *
          Real.log (2 * Real.exp (p * delta) / constrainedCqShell pi (fun a : A => f a.val) E n delta))))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
