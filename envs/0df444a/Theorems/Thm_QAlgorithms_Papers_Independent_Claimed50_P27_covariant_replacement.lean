-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P27_covariant_replacement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P27.covariant_replacement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:18:56.528994+00:00
-- url     : https://prove2.me/theorems/6b1a2e5b-4eae-4f24-b5f1-f8bac3fa33da
-- title:
--   Covariant replacement preserving cloning fidelity
-- statement:
--   Let $d\ge2$ and let $R$ be an admissible one-use unitary-cloning Choi operator: $R\succeq0$, $\operatorname{Tr}_3R=I_2\otimes R_0$ and $\operatorname{Tr}_1R_0=I_0$. Use the normalized Haar-average global fidelity $F$ of Eq. (4). There is another admissible operator $\widetilde R$ such that $F(\widetilde R)=F(R)$ and
--
--   $$[\widetilde R,V_0^{\otimes2}\otimes\overline V_1\otimes\overline W_2\otimes W_3^{\otimes2}]=0\qquad(V,W\in SU(d)).$$
--
--   The factors have the fixed wire order $0,1,2,3$, with doubled external factors at $0$ and $3$; the bars are entrywise conjugation in the computational bases. Consequently every optimizer has an equally good covariant replacement. This does not assert that every optimizer is itself covariant.
--
--   The stronger formulation for arbitrary admissible $R$ is exactly the fidelity-preserving averaging operation used in the source proof.
-- source:
--   Optimal cloning of unitary transformations, arXiv:0804.0129v2, PDF p. 2, Lemma 1; proof concludes p.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.2–3, Lemma 1 and its proof: every admissible network admits an equally
faithful covariant replacement. In particular this holds for every optimizer;
the optimizer itself is not asserted to commute with the action. -/
theorem covariant_replacement (d : ℕ) (hd : 2 ≤ d)
    (R : Matrix (CombReg d) (CombReg d) ℂ) (hR : CloningAdmissible R) :
    ∃ S : Matrix (CombReg d) (CombReg d) ℂ,
      CloningAdmissible S ∧ combScore S = combScore R ∧ CloningCovariant S := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P27

end
