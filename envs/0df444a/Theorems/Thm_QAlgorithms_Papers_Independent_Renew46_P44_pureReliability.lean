-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_pureReliability
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.pureReliability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:29:11.941689+00:00
-- url     : https://prove2.me/theorems/2ac1d99c-ebed-4b00-beab-397d7988161f
-- title:
--   §III.2, (38)–(43): random-coding and expurgated reliability bounds
-- statement:
--   For a normalized pure-state alphabet and product-letter codes, define $C$ to be operational average-error capacity and
--
--   $$E(R)=\limsup_{n\to\infty}\frac1n\log\frac1{p(n,\lceil e^{nR}\rceil)},\quad 0<R<C.$$
--
--   Zero error contributes $+\infty$. For a discrete prior $\pi$, put $\mu(\pi,0)=0$, $\mu(\pi,s)=-\log\operatorname{Tr}\bar S_\pi^{1+s}$ for $s>0$, and
--   $\widetilde\mu(\pi,s)=-s\log\sum_{a,b}\pi_a\pi_b|\langle\psi_a,\psi_b\rangle|^{2/s}$. Then
--
--   $$E(R)\ge\sup_{0\le s\le1}\sup_\pi(\mu(\pi,s)-sR),\qquad
--   E(R)\ge\sup_{s\ge1}\sup_\pi(\widetilde\mu(\pi,s)-sR).$$
--
--   The extended right slope at zero satisfies
--
--   $$C\ge\sup_\pi\mu'_+(\pi,0)=\sup_\pi\Delta H(\pi).$$
--
--   At every positive rate below $C$, the infimum error using the square-root decision rule itself tends to zero. These are lower bounds on reliability, with no claim that reliability equals either bound. Infinite entropy is represented by an infinite right slope. The cutoff endpoints also agree: $\widetilde C=\sup_\pi\mu(\pi,1)=\sup_\pi\widetilde\mu(\pi,1)$.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 13, §III.2, (38)–(43): random-coding and expurgated reliability bounds

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

/-- PDF pp.12-14, (38)-(43): both optimized reliability LOWER bounds and
entropy-slope capacity. Limsup and the square-root receiver achievability claim
are preserved; no equality with the true reliability function is asserted. -/
theorem pureReliability {A I : Type} [Nonempty A] [Nonempty I]
    (psi : A → Hilbert I) (hpsi : ∀ a, ‖psi a‖ = 1) :
    (∀ R : ℝ, 0 < R → ENNReal.ofReal R <
      averageErrorCqCapacity (fun a => TC.rankOne (psi a)) (fun _ => 0) 0 →
      (⨆ s : Set.Icc (0 : ℝ) 1, ⨆ pi : DiscreteInputLaw A,
        ENNReal.ofReal (pureMu psi pi s.val - s.val * R)) ≤
          reliability (fun a => TC.rankOne (psi a)) (fun _ => 0) 0 R ∧
      (⨆ s : Set.Ici (1 : ℝ), ⨆ pi : DiscreteInputLaw A,
        ENNReal.ofReal (pureExpurgatedMu psi pi s.val - s.val * R)) ≤
          reliability (fun a => TC.rankOne (psi a)) (fun _ => 0) 0 R ∧
      Tendsto (fun n : ℕ => squareRootCodeError psi n (natMessagesNats n R)) atTop (nhds 0)) ∧
    pureCutoffRate psi = (⨆ pi : DiscreteInputLaw A, ENNReal.ofReal (pureMu psi pi 1)) ∧
    pureCutoffRate psi = (⨆ pi : DiscreteInputLaw A, ENNReal.ofReal (pureExpurgatedMu psi pi 1)) ∧
    (⨆ pi : DiscreteInputLaw A, entropySlope psi pi) =
      (⨆ pi : DiscreteInputLaw A, discreteHolevoInformation (fun a => TC.rankOne (psi a)) pi) ∧
    (⨆ pi : DiscreteInputLaw A, entropySlope psi pi) ≤
      averageErrorCqCapacity (fun a => TC.rankOne (psi a)) (fun _ => 0) 0 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
