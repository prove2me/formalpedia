-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_fermion_entropy_pressure_condition
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.fermion_entropy_pressure_condition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:47:30.469469+00:00
-- url     : https://prove2.me/theorems/d6dbd22d-2692-4e8f-8faa-ab937c3b5803
-- title:
--   Proposition 4 (4.19)–(4.21) and Condition 1: fermion entropy and pressure limits
-- statement:
--   Let $d\ge1$, and let measurable Fourier symbols $\widehat q,\widehat r$ on $[0,2\pi)^d$ take values essentially in $[\delta,1-\delta]$, where $0<\delta<1/2$. Use normalized Lebesgue measure $dm=(2\pi)^{-d}dx$ and Fourier matrix entries $\int e^{-i\langle j-k,x\rangle}\widehat q(x)\,dm(x)$. Compress these multipliers to $\Lambda_n=\{0,\ldots,n-1\}^d$, obtaining $Q_n,R_n$, and form their quasi-free finite Fock densities $\rho_n,\sigma_n$ as in (4.16), including all particle-number sectors. Then
--   $$\lim_{n\to\infty}\frac{D(\rho_n\Vert\sigma_n)}{n^d}=d(\widehat\rho,\widehat\sigma)=\int\left[\widehat q\log\frac{\widehat q}{\widehat r}+(1-\widehat q)\log\frac{1-\widehat q}{1-\widehat r}\right]dm,$$
--   and, for every real $s$,
--   $$\lim_{n\to\infty}\frac{\Psi_s(\rho_n\mid\sigma_n)}{n^d}=\int\log\left(\widehat q^s\widehat r^{1-s}+(1-\widehat q)^s(1-\widehat r)^{1-s}\right)dm.$$
--   The pair sequence satisfies Condition 1 with weights $w_n=n^d$.
--
--   This retains the entropy and pressure limits and the analytic condition without adding smoothness or finite correlation length. The separate disputed boundary remainder is deferred.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 23, Proposition 4 (4.19)–(4.21) and Condition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P02

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate positiveMatrixRpow modularMatrix modularQuadratic resolventOverlap petzOverlap
    finiteRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower testingBeta)

open QAlgorithms.Papers.Independent.Information100.P58 (normalQuantile)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Proposition 4, PDF pp.23--25, (4.19)--(4.21) and Condition 1 ONLY.
Symbols need only be measurable and essentially separated from 0 and 1.
The false boundary estimate (4.23) and its dependent remarks are explicitly deferred. -/
theorem fermion_entropy_pressure_condition (d : ℕ) (hd : 1 ≤ d)
    (qhat rhat : (Fin d → ℝ) → ℝ) (hq : Measurable qhat) (hr : Measurable rhat)
    (delta : ℝ) (hdelta : 0 < delta ∧ delta < 1/2)
    (hgap : ∀ᵐ x ∂torusMeasure d,
      delta ≤ qhat x ∧ qhat x ≤ 1-delta ∧ delta ≤ rhat x ∧ rhat x ≤ 1-delta) :
    Tendsto (fun k => finitePairRelativeEntropyNats ((fermionSequence qhat rhat).rho k)
        ((fermionSequence qhat rhat).sigma k) / fermionWeight d k)
      atTop (nhds (symbolEntropy qhat rhat)) ∧
    relativeEntropyRate (fermionSequence qhat rhat) (fermionWeight d) = symbolEntropy qhat rhat ∧
    (∀ s : ℝ, Tendsto (fun k => realPetzLogOverlap ((fermionSequence qhat rhat).rho k)
        ((fermionSequence qhat rhat).sigma k) s / fermionWeight d k)
      atTop (nhds (symbolPressure qhat rhat s))) ∧
    ConditionOne (fermionSequence qhat rhat) (fermionWeight d) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
