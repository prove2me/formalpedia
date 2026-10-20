-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_separateErrorConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P67.separateErrorConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:05:01.041725+00:00
-- url     : https://prove2.me/theorems/eafeedb4-81ed-428b-8d1f-be10bb36908b
-- title:
--   Unnumbered consequence for separate errors (D.17)
-- statement:
--   Fix a finite-dimensional channel dilation and optimized exponential witnesses $\gamma>0,n_0$ at a threshold $q$ and gap $\Delta>0$. For every valid code satisfying $n\ge n_0$ and $\log_2M\ge n(q+\Delta)$, define $p_{\rm err}=\Pr\{K\ne\widehat K\}$ under its uniform prior and $\delta_{\rm sec}=\tfrac12\|\omega_{KE}-\pi_K\otimes\omega_E\|_1$, using the actual environment marginal. Then
--
--   $$p_{\rm err}+\delta_{\rm sec}\ge1-2^{-\gamma n/2}.$$
--
--   This uses exactly the optimized witnesses and applies in particular to the degradable, antidegradable, and erasure conclusions. Only the sum is bounded; neither individual error is asserted to approach one unconditionally.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 48, Unnumbered consequence for separate errors (D.17)

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

/-- Separate-error consequence (D.17), PDF p.49: the SUM tends to one,
with the same witnesses as the optimized bound and exponent gamma/2. -/
theorem separateErrorConverse [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U)
    (q gap gamma : ℝ) (hgap : 0 < gap) (hgamma : 0 < gamma) (n0 : ℕ)
    (hdecay : OptimizedDecay U q gap gamma n0) :
    ∀ n ≥ n0, ∀ code : PrivateCode A B n, code.Valid →
      (n : ℝ) * (q + gap) ≤ Real.logb 2 code.M →
      1 - Real.rpow 2 (-gamma * n / 2) ≤ decodingError U code + secrecyError U code := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
