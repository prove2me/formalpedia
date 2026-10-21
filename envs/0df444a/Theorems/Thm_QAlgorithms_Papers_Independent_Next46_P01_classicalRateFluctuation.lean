-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P01_classicalRateFluctuation
-- name    : QAlgorithms.Papers.Independent.Next46.P01.classicalRateFluctuation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:34:05.837139+00:00
-- url     : https://prove2.me/theorems/119f0f3b-9112-4fe0-ae65-68c83403cbb9
-- title:
--   Classical Evans–Searles symmetry of full and local LDP rates
-- statement:
--   Let $X$ be a compact metric space with its Borel sigma-algebra, $\phi_t$ a jointly continuous real group of homeomorphisms, and $\omega$ a non-invariant Borel probability. Assume (Cl1)–(Cl3): $\omega_t=(\phi_t)_*\omega$ and $\omega$ are equivalent, $c^t=\log(d\omega_t/d\omega)\circ\phi_t$ has continuous representatives, and these representatives are differentiable at zero in the supremum norm. Assume an involutive homeomorphism $\iota$ preserves $\omega$ and reverses $\phi$. For $t>0$, let $P_t$ be the distribution of $c^t/t$ under $\omega$, and let $I:\mathbb R\to[0,+\infty]$ be lower semicontinuous.
--
--   If $(P_t)_{t>0}$ satisfies the full large-deviation principle at speed $t$ with rate $I$, then
--   $$
--   I(-s)=I(s)+s\qquad(s\in\mathbb R).
--   $$
--   If instead it satisfies the local large-deviation principle on $(-a,a)$ for some $a>0$, the same identity holds for every $s\in(-a,a)$. The identity uses extended-real addition, so infinite rates remain infinite.
--
--   This is the rate fluctuation relation induced by the finite-time classical Evans–Searles law; it does not require the differentiable cumulant criterion of Theorem 2.5.
-- source:
--   Entropic Fluctuations in Statistical Mechanics II. Quantum Dynamical Systems, arXiv:2409.15485v2, PDF p. 22, §2.6, paragraph after Theorem 2.14: classical extension of Proposition 2.6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P01

noncomputable section

open Filter MeasureTheory Set

open scoped BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P01

section Classical

variable (X : Type*) [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

variable {X}

/-- Classical extension of Proposition 2.6: arXiv:2409.15485v2, PDF p.22,
paragraph after Theorem 2.14. This is the full and symmetric-local LDP rate
symmetry, beyond the finite-time RN identity. No Gartner--Ellis transform,
rate convexity, unique NESS, or quantum modular model is assumed. -/
theorem classicalRateFluctuation (D : RegularClassicalSystem X)
    (hnoninvariant : ClassicalNonInvariant D.toClassicalFlowSystem)
    (iota : X ≃ₜ X) (htri : ClassicalTRI D.toClassicalFlowSystem iota)
    (rate : ℝ → ℝ≥0∞) :
    (HasSpeedLDPOn (classicalRescaledLaw D) rate Set.univ →
      ∀ s : ℝ, (rate (-s) : EReal) = (rate s : EReal) + (s : EReal)) ∧
    (∀ a : ℝ, 0 < a →
      HasSpeedLDPOn (classicalRescaledLaw D) rate (Set.Ioo (-a) a) →
        ∀ s : ℝ, s ∈ Set.Ioo (-a) a →
          (rate (-s) : EReal) = (rate s : EReal) + (s : EReal)) := by sorry

end Classical

end QAlgorithms.Papers.Independent.Next46.P01

end
