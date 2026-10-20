-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_recoverableSingleFilter
-- name    : QAlgorithms.Papers.Independent.Information100.P67.recoverableSingleFilter
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:55:46.10783+00:00
-- url     : https://prove2.me/theorems/2ee4b184-f58e-42c0-a862-48ff4d3f42e0
-- title:
--   Lemma 5.1 (A recoverable single filter)
-- statement:
--   Let $|\psi\rangle_{ABR}$ be a normalized pure state on positive-dimensional finite systems and let $0<\delta<1/2$. There exist a positive-dimensional system $C$, one linear map $Z:A\to C$, and a CPTP recovery $\mathcal R:CB\to AB$. Set $\nu=\|(Z\otimes I_{BR})\psi\|^2$ and $|\chi\rangle=(Z\otimes I_{BR})|\psi\rangle/\sqrt\nu$. They satisfy
--
--   $$\nu>0,\qquad P((\mathcal R\otimes\mathrm{id}_R)(\chi),\psi)\le\delta,$$
--   $$\log_2|C|\le\left[H_{\max}^{\delta^2/16}(A|B)_\psi+4\log_2(1/\delta)+4\right]_++1.$$
--
--   Here $P=\sqrt{1-F}$ on normalized states, $F$ is squared fidelity, and the max-entropy smoothing ball contains subnormalized PSD states with purified distance at most the specified parameter. Recovery preserves all correlations with $R$. The filter is applied to the original state and no lower bound on its implementation probability is asserted.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 24, Lemma 5.1 (A recoverable single filter)

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

/-- Lemma 5.1, PDF pp.24–27. Recovery reconstructs AB and preserves R;
smoothing is delta^2/16 and the filter acts on the ORIGINAL normalized psi. -/
theorem recoverableSingleFilter [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ ((A × B) × R)) (hpsi : IsState psi)
    (delta : ℝ) (hd0 : 0 < delta) (hd1 : delta < 1 / 2) :
    ∃ L : ℕ, 0 < L ∧ ∃ Z : Matrix (Fin L) A ℂ,
      ∃ rec : Superop (Fin L × B) (A × B), FilterGuarantee psi delta L Z rec := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
