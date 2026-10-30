-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_cartan_generator_norm
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.cartan_generator_norm
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:23:32.392479+00:00
-- url     : https://prove2.me/theorems/409cb250-926b-404e-9984-b8f84d73433e
-- title:
--   Lemma 17: norm of the specified Cartan generator
-- statement:
--   Let $d\ge2$ and let $\lambda$ be a Young diagram with at most $d$ rows, normalized to have empty last row. Realize its irreducible representation as the image of the Young symmetrizer in tensor space, with the inherited Hilbert inner product. Let $T_\lambda$ be the restriction of the sum of cell actions of $T=\operatorname{diag}(1,0,\ldots,0,-1)$. Then $$\|T_\lambda\|_{\rm op}\le\lambda_1.$$ The specified Cartan generator and its scale are part of the construction.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 56, Lemma 17: norm of the specified Cartan generator

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.56, Lemma 17: the fixed Cartan generator in the actual normalized irrep.
The generator cannot be replaced by an arbitrary rescaling. -/
theorem cartan_generator_norm {d n : ℕ} (hd : 2 ≤ d)
    (lambda : QAlgorithms.Schur.Partition d n) (hlast : lambda.val.rowLen (d - 1) = 0) :
    ‖schurCartan lambda‖ ≤ (lambda.val.rowLen 0 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
