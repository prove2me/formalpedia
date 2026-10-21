-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P27_fidelity_one_iff_exact
-- name    : QAlgorithms.Papers.Independent.Claimed50.P27.fidelity_one_iff_exact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:19:35.476906+00:00
-- url     : https://prove2.me/theorems/d6e5a054-2dba-4e94-a8f4-fb57e561000a
-- title:
--   Fidelity one characterizes exact cloning everywhere
-- statement:
--   Let $d\ge2$ and let $R$ be an admissible finite one-use unitary-cloning network, with resulting channel $C_U$ after inserting $U$. Let $F(R)$ be the probability-Haar average of the normalized global channel fidelity. Then
--
--   $$0\le F(R)\le1,\qquad F(R)=1\ \Longleftrightarrow\ \forall U\in U(d),\ C_U=\mathcal U\otimes\mathcal U.$$
--
--   The equality of channels is expressed by equality of their unnormalized Choi operators in the same input-first external wire order. The conclusion holds for every gate, because the fixed finite network gives a continuous gate-dependent family. This is a characterization of exact cloning, rather than only an almost-everywhere characterization.
-- source:
--   Optimal cloning of unitary transformations, arXiv:0804.0129v2, PDF p. 2, Paragraph following Eq. (4)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.2, after Eq.(4): admissible scores lie in [0,1], and score one is
exact cloning for every gate. The finite comb enforces continuity, so the
conclusion is everywhere, not merely Haar-almost everywhere. -/
theorem fidelity_one_iff_exact (d : ℕ) (hd : 2 ≤ d)
    (R : Matrix (CombReg d) (CombReg d) ℂ) (hR : CloningAdmissible R) :
    (0 ≤ combScore R ∧ combScore R ≤ 1) ∧
    (combScore R = 1 ↔ ∀ U : (Matrix.unitaryGroup (Fin d) ℂ),
      insertedChoi R U = channelChoi (targetChannel U)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P27

end
