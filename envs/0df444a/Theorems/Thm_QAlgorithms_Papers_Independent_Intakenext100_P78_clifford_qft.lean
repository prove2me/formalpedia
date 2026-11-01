-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P78_clifford_qft
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P78.clifford_qft
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:56:19.325981+00:00
-- url     : https://prove2.me/theorems/0cab9460-b2f8-4f80-b81d-4fb3e2db5085
-- title:
--   Finite signed Clifford monomial groups: a polylogarithmic ideal QFT
-- statement:
--   Let $n\ge2$ and let $\mathrm{CL}_n$ be the finite group of signed monomials in involutions $x_1,\ldots,x_n$, with central sign $-1$ and $x_ix_j=-x_jx_i$ for $i\ne j$. Its order is $2^{n+1}$. Encode a group element as $(-1)^s x_n^{u_n}\cdots x_1^{u_1}$. Fix the explicit adapted representation coordinates: all $2^n$ linear characters, together with one nonlinear representation of dimension $2^{n/2}$ at even rank, or two of dimension $2^{(n-1)/2}$ at odd rank. In the nonlinear sectors the successive generators have tensor forms $Y^{\otimes r}\otimes Z$ and $Y^{\otimes r}\otimes X$, with identity factors after the indicated position; at odd rank the last generator is $\pm Y^{\otimes\lfloor n/2\rfloor}$.
--
--   There exist absolute $C>0$ and $k\in\mathbb N$ such that, for every $n\ge2$, a single clean ideal one- and two-qubit circuit has at most
--
--   $$C(n+2)^k$$
--
--   gates and, for every $f$ satisfying $\sum_g|f(g)|^2=1$, outputs the Fourier amplitudes
--
--   $$\widehat f(\rho)_{i,j}=\sqrt{\frac{d_\rho}{2^{n+1}}}\sum_g f(g)\rho(g)_{i,j}.$$
--
--   The circuit is independent of $f$. Since $n+2=1+\log_2|\mathrm{CL}_n|$, this is the source's polylogarithmic gate bound. The central-sign level is present in the encoding; no exact maximum-index assertion at the abbreviated bottom of the printed tower is used.
-- source:
--   Generic Quantum Fourier Transforms, arXiv:quant-ph/0304064v1, PDF p. 8, Unnumbered application: finite Clifford monomial groups

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P78

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P78

open QAlgorithms

attribute [local instance] Classical.propDecidable

/-- PDF p.8, unnumbered finite-Clifford-group application: a family-wide
polylogarithmic ideal QFT bound, since log2|CL_n|=n+1.
Source correction: the printed relation x_i x_j=-x_i x_j is read as
x_i x_j=-x_j x_i, as required by the cited Clifford group and the proof's
centralization of the earlier generators. The central-sign tower level is
included; no literal bottom-index-2 assertion is made. Independent moderation
of this correction is required. -/
theorem clifford_qft :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, n + 1 ≤ q ∧ ∃ c : Circuit oneTwoQubitGateSet q,
        (c.size : ℝ) ≤ C * ((n + 2 : ℕ) : ℝ) ^ k ∧
        realizesEncodedTransform c (cliffordInputCode n q) (cliffordOutputCode n q)
          cliffordFourier := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P78

end
