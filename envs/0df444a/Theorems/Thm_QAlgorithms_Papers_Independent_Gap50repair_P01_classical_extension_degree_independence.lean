-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_classical_extension_degree_independence
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.classical_extension_degree_independence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:32:16.038752+00:00
-- url     : https://prove2.me/theorems/75ab9ded-e6a2-4b8a-99ee-291faf0d776e
-- title:
--   Lemma 34
-- statement:
--   Let $n\ge1$ and let $\gamma:[0,1]\to\operatorname{Sp}(2n,\mathbb R)$ be continuous, with $\gamma(0)=I$ and $\det(\gamma(1)-I)\ne0$. Let $e_1,e_2:[0,2]\to\operatorname{Sp}(2n,\mathbb R)$ be admissible extensions: they agree with $\gamma$ on $[0,1]$, avoid eigenvalue $1$ on $[1,2]$, and end at one of the fixed representatives $W^+=-I$ or $W^-=\operatorname{diag}(2,-1,\ldots,-1,1/2,-1,\ldots,-1)$. For the source rotation map $\rho$,
--
--   $$\deg(\rho^2\circ e_1)=\deg(\rho^2\circ e_2).$$
--
--   Degree is oriented integer winding, with a positive full turn of degree $+1$. This makes Definition 33 independent of every admissible extension choice.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 35, Lemma 34

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Lemma 34 ([11,12]), PDF pp.35–36: all admissible extension choices
have the same oriented integer degree. -/
theorem classical_extension_degree_independence {n : ℕ} (hn : 1 ≤ n)
    (p e1 e2 : ℝ → GroupedRealMatrix n) (hp : IsAdmissible p 1)
    (he1 : IsExtension p e1) (he2 : IsExtension p e2) :
    winding (fun t => spectralRotation (e1 t)^2) 2 =
      winding (fun t => spectralRotation (e2 t)^2) 2 := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
