-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_uniformMaximalComparison
-- name    : QAlgorithms.Papers.Independent.Information100.P67.uniformMaximalComparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:05:39.439635+00:00
-- url     : https://prove2.me/theorems/20abe5bf-074e-4d17-894b-53298a152fbd
-- title:
--   Unnumbered finite-error comparison (2.12)–(2.15)
-- statement:
--   For every valid unassisted $(n,M)$ code and every common normalized environment matrix $\sigma$, let $\omega^m_{\widehat KE}$ be its messagewise output, $\omega_{K\widehat KE}$ the uniform output, and $\Phi^M_{\rm classical}$ the perfectly correlated uniform classical key. The squared-fidelity block identity is
--
--   $$F(\omega,\Phi^M_{\rm classical}\otimes\sigma)=\left(\frac1M\sum_m\sqrt{F(\omega^m,|m\rangle\langle m|\otimes\sigma)}\right)^2.$$
--
--   With optimization over a single common $\sigma$, it follows that $\varepsilon(\mathcal C_n)\le\varepsilon_{\max}(\mathcal C_n)$. This is a finite-error ordering, rather than equality of the criteria or an arithmetic mean of fidelities.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 7, Unnumbered finite-error comparison (2.12)–(2.15)

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

/-- The ideal-key block-fidelity identity and uniform/maximal comparison,
(2.12)–(2.15), PDF p.7. -/
theorem uniformMaximalComparison [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U) {n : ℕ}
    (code : PrivateCode A B n) (hc : code.Valid) :
    (∀ sigma : Matrix (Fin n → E) (Fin n → E) ℂ, IsDensityMatrix sigma →
      squaredFidelity (jointOutput U code) (idealJoint code.M sigma) =
        (((code.M : ℝ)⁻¹ * ∑ m : Fin code.M,
          Real.sqrt (squaredFidelity (messageOutput U code m) (idealMessage m sigma))) ^ 2)) ∧
    uniformError U code ≤ maximalError U code := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
