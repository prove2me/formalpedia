-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P74_erasure_key_rate
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P74.erasure_key_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:12:29.437106+00:00
-- url     : https://prove2.me/theorems/be8515c4-2ca4-486a-9905-877ec611a13e
-- title:
--   Erasure-channel sufficient criterion for vanishing key rate
-- statement:
--   Let $\epsilon\in[0,1]$ and consider the complementary qubit erasure wiretap dilation
--
--   $$
--   V|a\rangle=\sqrt{1-\epsilon}|a\rangle^B|e\rangle^E+
--   \sqrt\epsilon|e\rangle^B|a\rangle^E,
--   $$
--
--   where $a\in\{0,1\}$ and $|e\rangle$ is orthogonal to both input basis states. Use uniform computational-basis inputs and trivial shields. Bob's amplitude and virtual phase channels satisfy
--
--   $$
--   \sqrt{F(W_{A,B})}=\sqrt{F(W_{P,B})}=\epsilon,
--   \qquad I(W_{A,B})-I(W_{A,E})=1-2\epsilon.
--   $$
--
--   For every fixed $0<\beta<1/2$, the polar code defined above consequently satisfies
--
--   $$
--   2\epsilon<1\quad\Longrightarrow\quad
--   \lim_{n\to\infty}\frac{|\mathcal B_{2^n}|}{2^n}=0.
--   $$
--
--   Thus the criterion applies exactly when this symmetric private information is positive. This is a finite-register erasure result, without a bosonic energy constraint.
-- source:
--   Polar codes for private classical communication, arXiv:1203.5794v1, PDF p. 10, Appendix C.B, unnumbered: erasure-channel criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P74

namespace QAlgorithms.Papers.Independent.Intakethird100.P74

open QAlgorithms

open scoped ComplexConjugate Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {B E S1 S2 : Type}

variable [Fintype B] [Fintype E] [Fintype S1] [Fintype S2]

variable [DecidableEq B] [DecidableEq E] [DecidableEq S1] [DecidableEq S2]

/-- PDF pp.9–10, Appendix C.B: both initial root fidelities are eps and the strict
criterion 2eps<1 gives vanishing key rate, precisely where symmetric private information
is positive. Source correction: p.10's phase-mixture display swaps eps and 1-eps;
the defining erasure map, its discrimination argument and its final criterion fix the
weights used here. Independent moderation of this correction remains required. -/
theorem erasure_key_rate (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1 / 2) :
    rootFidelity (amplitudeBob (erasureData eps) false)
      (amplitudeBob (erasureData eps) true) = eps ∧
    rootFidelity (phaseBob (erasureData eps) false)
      (phaseBob (erasureData eps) true) = eps ∧
    symmetricPrivateInformation (erasureData eps) = 1 - 2 * eps ∧
    (2 * eps < 1 → Filter.Tendsto (keyRate (erasureData eps) beta) Filter.atTop (nhds 0)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P74
