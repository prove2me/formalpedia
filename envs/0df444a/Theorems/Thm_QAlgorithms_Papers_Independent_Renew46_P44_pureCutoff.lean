-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_pureCutoff
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.pureCutoff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:27:30.039477+00:00
-- url     : https://prove2.me/theorems/4286c136-951e-448a-8a3d-15c6e3b7a645
-- title:
--   §III.1, (33)–(34): random-code collision bound and cutoff rate
-- statement:
--   Let $a\mapsto|\psi_a\rangle$ be a normalized pure-state alphabet on a nonzero Hilbert space, and let $\pi$ be any discrete probability law. Put $\bar S_\pi=\sum_a\pi_a|\psi_a\rangle\langle\psi_a|$ and $b_\pi=\operatorname{Tr}\bar S_\pi^2=\sum_{a,b}\pi_a\pi_b|\langle\psi_a,\psi_b\rangle|^2$. Independently sample $M\ge1$ words of length $n\ge1$, each with the product law $\pi^{\otimes n}$. Then
--
--   $$\mathbb E S_w=\bar S_\pi^{\otimes n},\qquad p(n,M)\le\mathbb E\inf_X\bar\lambda(W,X)\le(M-1)b_\pi^n.$$
--
--   Consequently, with extended suprema and operational average-error capacity $C$,
--
--   $$C\ge\widetilde C:=\sup_\pi[-\log b_\pi]=-\log\inf_\pi b_\pi.$$
--
--   No entropy finiteness is needed. The power $b_\pi^n$ corrects the printed exponential sign. The separate incorrect assertion of strictness for all noncommuting alphabets is excluded, as pinned in the plan.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 11, §III.1, (33)–(34): random-code collision bound and cutoff rate

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

/-- PDF p.11, (33)-(34): iid collision bound and cutoff achievability.
Printed exp(-n log Tr(Sbar^2)) has the wrong sign: use (Tr(Sbar^2))^n,
as forced by the preceding tensor trace and the displayed cutoff definition.
The asserted strictness for every noncommuting alphabet is deferred separately. -/
theorem pureCutoff {A I : Type} [Nonempty A] [Nonempty I]
    (psi : A → Hilbert I) (hpsi : ∀ a, ‖psi a‖ = 1) :
    (∀ (pi : DiscreteInputLaw A) (n M : ℕ), 0 < n → 0 < M →
      (∀ i j : Fin n → I,
        (∑' w : Fin n → A, (wordWeight pi w : ℂ) *
          wordOutput (fun a => TC.rankOne (psi a)) w i j) =
        ∏ k, discreteStateAverage (fun a => TC.rankOne (psi a)) pi (i k) (j k)) ∧
      cqError (fun a => TC.rankOne (psi a)) (fun _ => 0) 0 n M ≤
        expectedDecodingError (fun a => TC.rankOne (psi a)) pi n M ∧
      expectedDecodingError (fun a => TC.rankOne (psi a)) pi n M ≤
        ENNReal.ofReal (((M : ℝ) - 1) * pureCollisionTrace psi pi ^ n)) ∧
    (∀ pi : DiscreteInputLaw A, pureMeanPowerTrace psi pi 1 = pureCollisionTrace psi pi) ∧
    pureCutoffRate psi ≤ averageErrorCqCapacity (fun a => TC.rankOne (psi a)) (fun _ => 0) 0 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
