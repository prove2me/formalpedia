-- Prove2me | Theorems.Thm_UnivESD_Universality_lemma_A_2
-- name    : UnivESD.Universality.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:23.354764+00:00
-- url     : https://prove2.me/theorems/052e04fd-f928-4668-9bd3-26e1dbb19202
-- title:
--   Lemma A.2 (Weyl comparison inequality for second moment): $\sum|\lambda_j|^2\le\sum\sigma_j(A)^2=\|A\|_2^2$
-- statement:
--   Let $A=(a_{ij})_{1\le i,j\le n}\in M_n(\mathbb C)$ have generalized eigenvalues $\lambda_1,\dots,\lambda_n\in\mathbb C$ (counted with algebraic multiplicity) and singular values $\sigma_1(A)\ge\cdots\ge\sigma_n(A)\ge0$. Then
--   $$\sum_{j=1}^n|\lambda_j|^2\le\sum_{j=1}^n\sigma_j(A)^2=\|A\|_2^2=\sum_{i=1}^n\sum_{j=1}^n|a_{ij}|^2,$$
--   where $\|A\|_2^2=\mathrm{trace}(AA^*)$.
--
--   The inequality bounds the second moment of the ESD by the Hilbert–Schmidt norm; it is what turns the size condition (1.3) into tightness of the ESDs (Lemma 1.7).
--
--   **Formalization Note.** The eigenvalues are the roots of the characteristic polynomial as a multiset; the two equalities are stated with $\|A\|_2^2$ written as $\mathrm{trace}(AA^*)$, and singular values are one-based.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2058 (PDF 36), Lemma A.2

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

open Matrix in
/-- Lemma A.2 (Weyl comparison inequality for second moment), p. 2058. Eigenvalues are the
roots of the characteristic polynomial with multiplicity; singular values are one-based. -/
theorem lemma_A_2 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (A.charpoly.roots.map fun l => ‖l‖ ^ 2).sum ≤ ∑ j ∈ Finset.Icc 1 n, singVal A j ^ 2 ∧
      (((∑ j ∈ Finset.Icc 1 n, singVal A j ^ 2 : ℝ)) : ℂ) = (A * Aᴴ).trace ∧
      (A * Aᴴ).trace = ((hsNormSq A : ℝ) : ℂ) := by sorry

end UnivESD.Universality
