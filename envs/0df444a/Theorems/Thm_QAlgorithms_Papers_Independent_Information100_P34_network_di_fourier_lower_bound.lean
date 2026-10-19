-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P34_network_di_fourier_lower_bound
-- name    : QAlgorithms.Papers.Independent.Information100.P34.network_di_fourier_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:58:36.895953+00:00
-- url     : https://prove2.me/theorems/b9193b9f-57ad-4e2e-94d6-0b04bc88b80d
-- title:
--   Lemma 24: network-DI lower bound for larger unitary targets
-- statement:
--   Let $d,D$ be positive integers with $D>d$, let $U$ be any $D$-dimensional unitary, and write $\mathcal U(X)=UXU^\dagger$. Every DI network $\mathcal S$ with one input slot satisfies
--
--   $$\frac12\|\mathcal S[\mathcal F_d]-\mathcal U\|_\diamond\ge\min_{0\le i,j<D}|U_{ij}|^2.$$
--
--   Here the network is operationally $\mathcal M_1\circ(\mathrm{id}_R\otimes\mathcal F_d)\circ\mathcal M_0$, with arbitrary finite positive memory $R$ and DI pre- and postprocessing channels. The diamond distance optimizes over normalized input states with an input-sized reference. The bound allows zero entries of $U$ and thus need not be strictly positive.
-- source:
--   The Structure of Higher-Order Quantum Resources with an Application to Coherence, arXiv:2609.40186v1, PDF p. 40, Lemma 24

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

/-- Lemma 24, Eq.(C133), PDF pp.40-41. Quantification over all finite
positive memories and all DI pre/postprocessings is exactly the network class.
The Fourier slot is substituted operationally; the lower bound can be zero. -/
theorem network_di_fourier_lower_bound {d D : ℕ} (hd : 0 < d) (hDd : d < D)
    (U : Matrix.unitaryGroup (Fin D) ℂ) :
    ∀ r : ℕ, 0 < r →
    ∀ pre : Superop (Fin D) (Fin r × Fin d),
    ∀ post : Superop (Fin r × Fin d) (Fin D),
      Free .di pre → Free .di post →
      smallestEntrySq (lt_trans hd hDd) (U : Matrix (Fin D) (Fin D) ℂ) ≤
        diamondDistance (post ∘ idTensorSuperop (R := Fin r) (fourierChannel d) ∘ pre)
          (conjSuperop (U : Matrix (Fin D) (Fin D) ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P34

end
