-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma5_3_kraus_block_form
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma5_3_kraus_block_form
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:44:00.54084+00:00
-- url     : https://prove2.me/theorems/eb0fb697-bdbd-489a-8099-0b6ec9f9f306
-- title:
--   Lemma 5.3: Kraus operators in canonical block form
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Choose any canonical orthogonal tensor decomposition of $P_0$ induced by $\operatorname{Fix}(\mathcal E_0^\dagger)$, and any Kraus representation of $\mathcal E$. Relative to $H=(\bigoplus_kA_k\otimes B_k)\oplus P_0^\perp$, every Kraus operator has the form
--
--   $$E_i=\begin{pmatrix}\bigoplus_k(I_{A_k}\otimes K_{i,k})&D_i\\0&C_i\end{pmatrix},\quad D_i:P_0^\perp\to P_0,\quad C_i:P_0^\perp\to P_0^\perp.$$
--
--   The factors $K_{i,k}$ exist as a conclusion; the other blocks are the actual corresponding compressions of $E_i$.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 23, Lemma 5.3: Kraus operators in canonical block form

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF p.23, Lemma 5.3, Eq.(B5), visually checked. D_i=P0 E_i(1-P0) and
C_i=(1-P0)E_i(1-P0) have the printed domains. The lower-left block vanishes.
The tensor form is a conclusion, not a premise. -/
theorem lemma5_3_kraus_block_form {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    (B : BlockModel I) (hB : IsFixedDecomposition E B)
    (m : ℕ) (K : Fin m → Op I) (hK : ∀ X, E X = krausApply K X) :
    ∃ L : (i : Fin m) → (k : Fin B.sectors) → Op (Fin (B.gaugeDim k)),
      ∀ i, (1 - B.support) * K i * B.support = 0 ∧
        K i = (∑ k, B.embed k * Matrix.kronecker (1 : Op (Fin (B.logicalDim k)))
          (L i k) * (B.embed k)ᴴ) + B.support * K i * (1 - B.support) +
            (1 - B.support) * K i * (1 - B.support) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
