-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_pureRandomCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.pureRandomCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:28:37.633985+00:00
-- url     : https://prove2.me/theorems/3327be33-61d4-41a8-83ac-a07dd31da698
-- title:
--   Theorem 2: pure-state random-coding bound
-- statement:
--   Let $a\mapsto|\psi_a\rangle$ be unit pure signals, let $\pi$ be a discrete probability law, and let $\bar S_\pi=\sum_a\pi_a|\psi_a\rangle\langle\psi_a|$. For independently sampled codewords with common product law $\pi^{\otimes n}$, every positive integer blocklength $n$, positive integer message count $M$, and $0\le s\le1$ satisfy
--
--   $$\mathbb E\inf_X\bar\lambda(W,X)\le2(M-1)^s\bigl[\operatorname{Tr}(\bar S_\pi^{1+s})\bigr]^n.$$
--
--   The infimum uses collective bounded sub-POVMs and uniform average error. The full trace is raised to $n$, including $s=0,1$ and $M=1$. This is a pure-signal random-coding estimate.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 12, Theorem 2: pure-state random-coding bound

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

/-- Theorem 2, PDF pp.12-13, (39). The ENTIRE trace is raised to n;
the signals are normalized pure states, with independently sampled codewords. -/
theorem pureRandomCoding {A I : Type} [Nonempty A] [Nonempty I]
    (psi : A → Hilbert I) (hpsi : ∀ a, ‖psi a‖ = 1)
    (pi : DiscreteInputLaw A) (n M : ℕ) (hn : 0 < n) (hM : 0 < M)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    expectedDecodingError (fun a => TC.rankOne (psi a)) pi n M ≤
      ENNReal.ofReal (2 * ((M : ℝ) - 1) ^ s * (pureMeanPowerTrace psi pi s) ^ n) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
