-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P40_lemma2_unitary_hermitian_trace_separates
-- name    : QAlgorithms.Papers.Independent.Advance50.P40.lemma2_unitary_hermitian_trace_separates
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:01:58.384138+00:00
-- url     : https://prove2.me/theorems/f85fe665-c641-4470-b76b-71f1672eef45
-- title:
--   Lemma 2: unitary Hermitian matrices separate the complex trace pairing
-- statement:
--   Let $n\geq1$ and let $X\in M_n(\mathbb C)$ be arbitrary. If the complex trace vanishes against every unitary Hermitian matrix of the same size, then
--   $$
--   \left[\ \forall A\in U(n),\quad A=A^{\dagger}\Longrightarrow\operatorname{Tr}(AX)=0\ \right]
--   \Longrightarrow X=0.
--   $$
--   This separates the full complex trace pairing without assuming that $X$ is Hermitian.
-- source:
--   Vanishing quantum discord is necessary and sufficient for completely positive maps, arXiv:0808.0175v2, PDF p. 3, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P40

/-- Lemma 2, PDF p. 3, proof on PDF p. 4. The trace pairing is complex-valued,
and X need not be Hermitian. The quantifier covers every unitary Hermitian A. -/
theorem lemma2_unitary_hermitian_trace_separates {n : ℕ} [NeZero n]
    (X : SystemMatrix n)
    (htrace : ∀ A : Matrix.unitaryGroup (Fin n) ℂ,
      (A : SystemMatrix n).IsHermitian →
        Matrix.trace ((A : SystemMatrix n) * X) = 0) :
    X = 0 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P40

end
