-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P34_unitary_dephasing_iff_monomial
-- name    : QAlgorithms.Papers.Independent.Information100.P34.unitary_dephasing_iff_monomial
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:27:15.724336+00:00
-- url     : https://prove2.me/theorems/135e3775-3627-45c3-b241-94373c673347
-- title:
--   Lemma 20: dephasing-commuting unitary channels are monomial
-- statement:
--   Let $d>0$ and let $U$ be a unitary matrix on a fixed $d$-dimensional computational basis. Write $\mathcal U(X)=UXU^\dagger$ and let $\Delta$ completely dephase that basis. Then
--
--   $$\mathcal U\circ\Delta=\Delta\circ\mathcal U\quad\Longleftrightarrow\quad U=P_\pi\operatorname{diag}(\omega_k),\qquad |\omega_k|=1\ \text{for every }k,$$
--
--   where $\pi$ is a permutation and column $k$ of $P_\pi$ is $|\pi(k)\rangle$. The equality on the left holds on every operator. This characterizes precisely the dephasing-commuting unitary channels.
-- source:
--   The Structure of Higher-Order Quantum Resources with an Application to Coherence, arXiv:2609.40186v1, PDF p. 34, Lemma 20

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

/-- Lemma 20, Eq.(C85), PDF pp.34-35: equality of channels on every operator. -/
theorem unitary_dephasing_iff_monomial {d : ℕ} (hd : 0 < d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (∀ X : Matrix (Fin d) (Fin d) ℂ,
      conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) (dephasing X) =
        dephasing (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) X)) ↔
    ∃ pi : Equiv.Perm (Fin d), ∃ omega : Fin d → ℂ,
      (∀ k, ‖omega k‖ = 1) ∧
      (U : Matrix (Fin d) (Fin d) ℂ) = permutationMatrix pi * Matrix.diagonal omega := by sorry

end QAlgorithms.Papers.Independent.Information100.P34

end
