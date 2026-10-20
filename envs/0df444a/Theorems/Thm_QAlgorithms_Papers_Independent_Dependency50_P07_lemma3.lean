-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_lemma3
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.lemma3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:24:27.369613+00:00
-- url     : https://prove2.me/theorems/7e9a8ca2-ec21-410a-9c5b-81cfe6f72915
-- title:
--   Attaining rate split for independent cq ensembles
-- statement:
--   Let $E_1$ and $E_2$ be finite classical–quantum ensembles on nonempty systems, and form their independent product ensemble. For each ensemble let $D^*(E,R)=\sup_{U|X}\{I(U;Q):I(U;X)-I(U;Q)\le R\}$. For $R\ge0$,
--
--   $$D^*(E_1\otimes E_2,R)=\max_{R_1,R_2\ge0,\ R_1+R_2=R}\bigl[D^*(E_1,R_1)+D^*(E_2,R_2)\bigr].$$
--
--   The maximum is attained by some nonnegative split, and every such split is bounded above by the product value. This is the product-ensemble identity used for iid single-letterization.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 7, Lemma 3: product-ensemble rate splitting

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section CQStatements

variable {X Q Y T : Type} [Fintype X] [Fintype Q] [Fintype Y] [Fintype T]
  [DecidableEq X] [DecidableEq Q] [DecidableEq Y] [DecidableEq T]
  [Nonempty X] [Nonempty Q] [Nonempty Y] [Nonempty T]

/-- PDF pp.7--8, Lemma 3: a maximizing nonnegative rate split, and dominance over every split. -/
theorem lemma3 (E : CQData X Q) (F : CQData Y T) (hE : E.Valid) (hF : F.Valid)
    (R : ℝ) (hR : 0 ≤ R) :
    (∃ R1 R2 : ℝ, 0 ≤ R1 ∧ 0 ≤ R2 ∧ R1 + R2 = R ∧
      dStar (productCQ E F) R = dStar E R1 + dStar F R2) ∧
    ∀ R1 R2 : ℝ, 0 ≤ R1 → 0 ≤ R2 → R1 + R2 = R →
      dStar E R1 + dStar F R2 ≤ dStar (productCQ E F) R := by sorry

end CQStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
