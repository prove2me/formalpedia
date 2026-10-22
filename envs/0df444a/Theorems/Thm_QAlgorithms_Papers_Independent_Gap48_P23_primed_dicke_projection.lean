-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_primed_dicke_projection
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.primed_dicke_projection
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:03:30.298926+00:00
-- url     : https://prove2.me/theorems/9165c6f8-aa0b-4e58-ae30-4919c53ce095
-- title:
--   Lemma D.6.
-- statement:
--   For $\ell\ge0$, $T^\ell(M)$ is the explicit $(\ell+1)$-dimensional normalized-monomial representation (C.9), evaluated on any complex $2\times2$ matrix. Its coordinates are indexed by $0,\ldots,\ell$. Let $V^\ell|w\rangle=|s_\ell(w)\rangle$ be the real Dicke embedding, $\Pi_\ell=V^\ell V^{\ell\dagger}$, and $|\psi^\ell\rangle=\sum_w\sqrt{\binom\ell w}\psi_0^{\ell-w}\psi_1^w|w\rangle$. Empty tensor powers are one-dimensional and $0^0=1$.
--
--   For $\ell\ge1$ and $0\le w<\ell$, define $|s'_{\ell-1}(w)\rangle=\sqrt{(w+1)/(\ell+1)}|0\rangle|s_\ell(w+1)\rangle-\sqrt{(\ell-w)/(\ell+1)}|1\rangle|s_\ell(w)\rangle$. Then
--   $$|s'_{\ell-1}(w)\rangle=\sqrt{\frac{2\ell}{\ell+1}}(I\otimes\Pi_\ell)(|\Psi^-\rangle\otimes|s_{\ell-1}(w)\rangle).$$
--   The singlet has the ordered positive $|01\rangle$ amplitude.
--
--   This supplies a concrete coordinate identity for the representation and symmetric-space constructions.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 69, Lemma D.6.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.69, Lemma D.6: the exact normalized projected-singlet formula. -/
theorem primed_dicke_projection (ell : ℕ) (hell : 1 ≤ ell) (w : Fin ell) :
    primedDicke ell w = (Real.sqrt (2*(ell:ℝ)/(ell+1)) : ℂ) •
      WithLp.toLp 2 ((Matrix.kronecker (1 : Op (Fin 2)) (dickeColumnProjector ell)).mulVec
        (singletDicke ell w)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
