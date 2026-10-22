-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_arbitrary_fock_decrement_locc
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.arbitrary_fock_decrement_locc
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:20:48.960075+00:00
-- url     : https://prove2.me/theorems/10045143-d835-43f0-8813-1642fe1ff76b
-- title:
--   Appendix 5b: arbitrary Fock decrement by explicit LOCC
-- statement:
--   Let $k\ge0$, let the integer $d\ge1$, and let $0<\lambda<1$. Write $p_n^{(k)}=(1-\lambda^2)^{k+1}\lambda^{2n}\binom{n+k}{n}$ and set $w_m=(1-\lambda^2)^d\binom{m+d-1}{d-1}\lambda^{2m}$. Bob's bounded countable measurement is
--
--   $$
--   B_m=\sum_{l\ge m}\sqrt{\frac{w_m p_{l-m}^{(k)}}{p_l^{(k+d)}}}\,|l-m\rangle\langle l|.
--   $$
--
--   Its completeness sum $\sum_m B_m^*B_m=I$ converges strongly. On input $|\Psi_\lambda^{(k+d)}\rangle$, the outcome law is $w_m$, which sums to one. Bob communicates $m$ to Alice, whose principal shift is $A_m=\sum_{l\ge0}|l\rangle\langle l+m+d|$. Adding Kraus operators $|0\rangle\langle j|$ for $0\le j<m+d$ makes her operation trace preserving on all local states. The exact branch law is
--
--   $$
--   (A_m\otimes B_m)|\Psi_\lambda^{(k+d)}\rangle=\sqrt{w_m}\,|\Psi_\lambda^{(k)}\rangle.
--   $$
--
--   All other terminal branches are scalar multiples of the same normalized target, and the local tensors have their physical matrix coefficients. Therefore the specified protocol is deterministic.
--
--   This retains the explicit arbitrary-decrement instrument rather than replacing it by repeated single steps. The case $d=0$ is separately the identity and is outside the displayed $d-1$ formula.
--
--   The conversion also holds at $\lambda=0$: the input is the product number state $|k+d,0\rangle$ (with $d=1$ in the one-photon case), and independent complete local reset instruments prepare $|k,0\rangle$. The displayed quotient-based measurement is used only for $0<\lambda<1$.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 9, Appendix 5b, (A.55)–(A.56)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF p.9, (A.55)-(A.56). The distinct arbitrary-d
instrument, its negative-binomial branch law, and conditional complete Alice
shift deterministically map |Psi(k+d)> to |Psi(k)>. d=0 is separately identity.
At lambda=0 use complete local resets between the product number states,
rather than the undefined coefficient ratios of the displayed instrument. -/
theorem arbitrary_fock_decrement_locc (k d : ℕ) (hd : 1 ≤ d)
    (lambda : ℝ) (hl : 0 ≤ lambda) (hlu : lambda < 1) :
    if lambda = 0 then
      ResetProtocol k (squeezed (k + d) lambda) (squeezed k lambda)
    else FockDecrementProtocol k d lambda := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
