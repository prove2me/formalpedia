-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_one_photon_locc
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.one_photon_locc
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:20:21.74611+00:00
-- url     : https://prove2.me/theorems/8c693d8a-b47b-4aae-857f-ffaf526f337b
-- title:
--   Appendix 5a: explicit one-photon-step deterministic LOCC
-- statement:
--   Fix $k\ge0$ and $0<\lambda<1$, and let $p_n^{(k)}=(1-\lambda^2)^{k+1}\lambda^{2n}\binom{n+k}{n}$. Starting from $|\Psi_\lambda^{(k+1)}\rangle$, Bob uses the countable measurement
--
--   $$
--   B_m=\sum_{l\ge m}\sqrt{\frac{(1-\lambda^2)\lambda^{2m}p_{l-m}^{(k)}}{p_l^{(k+1)}}}\,|l-m\rangle\langle l|,\qquad m\ge0.
--   $$
--
--   The bounded operators satisfy $\sum_m B_m^*B_m=I$ strongly. The probability of outcome $m$ is $w_m=(1-\lambda^2)\lambda^{2m}$ and these probabilities sum to one. Bob sends $m$ to Alice, who applies $A_m=\sum_{l\ge0}|l\rangle\langle l+m+1|$ on the occupied support. Extending this partial shift by the Kraus operators $|0\rangle\langle j|$, $0\le j<m+1$, gives a trace-preserving operation on her entire Fock space. Its principal branch satisfies
--
--   $$
--   (A_m\otimes B_m)|\Psi_\lambda^{(k+1)}\rangle=\sqrt{w_m}\,|\Psi_\lambda^{(k)}\rangle.
--   $$
--
--   Every terminal branch of the extended operation is an unnormalized scalar multiple of the same norm-one target. The tensor operations realize the actual local matrices.
--
--   Thus this specified Bob-to-Alice protocol converts the input deterministically to $|\Psi_\lambda^{(k)}\rangle$, with no assertion about a normalized zero-probability branch.
--
--   The conversion also holds at $\lambda=0$: the input is the product number state $|k+d,0\rangle$ (with $d=1$ in the one-photon case), and independent complete local reset instruments prepare $|k,0\rangle$. The displayed quotient-based measurement is used only for $0<\lambda<1$.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 9, Appendix 5a, (A.52)–(A.54)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF p.9, (A.52)-(A.54). Bob measures, communicates m,
and Alice applies the shift with a CPTP extension. All outcomes and the exact
geometric branch law are retained; no normalized vector is attached to a zero
probability branch. At lambda=0 the inputs and target are product number
states, and independent complete local resets give the conversion; the
zero-over-zero measurement formula is not used at this endpoint. -/
theorem one_photon_locc (k : ℕ) (lambda : ℝ) (hl : 0 ≤ lambda) (hlu : lambda < 1) :
    if lambda = 0 then
      ResetProtocol k (squeezed (k + 1) lambda) (squeezed k lambda)
    else FockDecrementProtocol k 1 lambda := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
