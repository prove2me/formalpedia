-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_actualMarginalExample
-- name    : QAlgorithms.Papers.Independent.Information100.P67.actualMarginalExample
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:04:29.254193+00:00
-- url     : https://prove2.me/theorems/0b7c8d14-fad5-436b-90df-69f49067d18e
-- title:
--   Unnumbered explicit example: optimized and actual-marginal fidelities differ (D.6)–(D.9)
-- statement:
--   Let $M\ge2$ and $0<p<1$. The dilation $|m\rangle\mapsto|m\rangle_{B_1}(\sqrt p|00\rangle+\sqrt{1-p}|11\rangle)_{B_0E}$ defines a degradable flagged identity channel. Consider the one-use code encoding $m$ as $|m\rangle$, measuring $B_1,B_0$ in their bases, and reporting $m$ on flag zero and its cyclic successor on flag one. This is a valid unassisted code. Its output is exactly
--
--   $$\omega=\frac1M\sum_m\left[p|mm\rangle\langle mm|\otimes|0\rangle\langle0|+(1-p)|m,m\oplus1\rangle\langle m,m\oplus1|\otimes|1\rangle\langle1|\right].$$
--
--   For every normalized environment matrix $\sigma$, $F(\omega,\Phi_{\rm classical}^M\otimes\sigma)=p\langle0|\sigma|0\rangle$. Consequently
--
--   $$f=p,\qquad f_{\rm marg}=p^2<p.$$
--
--   The environment marginal is the diagonal flag distribution. This concrete channel/code example shows that the two fidelities need not coincide.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 48, Unnumbered explicit example: optimized and actual-marginal fidelities differ (D.6)–(D.9)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Explicit degradable-channel counterexample (D.6)–(D.9), PDF p.48.
Both the channel and the actual code are constructed, not assumed to have
favorable output fidelities. M≥2 prevents the cyclic successor being correct. -/
theorem actualMarginalExample (M : ℕ) (hM : 2 ≤ M)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    let U := flaggedIdentityDilation M p
    let code := flaggedIdentityCode M
    IsDegradable U ∧ code.Valid ∧ jointOutput U code = flaggedExampleOutput M p ∧
    (∀ sigma : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ, IsDensityMatrix sigma →
      squaredFidelity (jointOutput U code) (idealJoint M sigma) =
        p * (sigma (fun _ => false) (fun _ => false)).re) ∧
    optimizedFidelity U code = p ∧ marginalFidelity U code = p ^ 2 ∧
    marginalFidelity U code < optimizedFidelity U code := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
