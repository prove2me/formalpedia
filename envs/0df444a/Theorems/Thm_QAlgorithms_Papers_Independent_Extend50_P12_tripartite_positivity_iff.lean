-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P12_tripartite_positivity_iff
-- name    : QAlgorithms.Papers.Independent.Extend50.P12.tripartite_positivity_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:49:46.673629+00:00
-- url     : https://prove2.me/theorems/3ea91856-9199-4fff-b89f-b5e64d5e6a36
-- title:
--   Proposition 4: exact tripartite positivity/block-positivity equivalences
-- statement:
--   Let $d\ge1$ and let $\rho$ be a PSD trace-one matrix on $(\mathbb C^d)^{\otimes3}$ invariant under conjugation by $U^{\otimes3}$ for every $d$-dimensional unitary $U$. Let $S$ be a proper subset of $\{1,2,3\}$, possibly empty, and write $T_S$ for ordinary partial transpose on those sites. Define
--   $$
--   f_S(A)=\operatorname{tr}_1[\rho^{T_S}(A\otimes I\otimes I)],\qquad
--   g_S(A,B)=\operatorname{tr}_{12}[\rho^{T_S}(A\otimes B\otimes I)].
--   $$
--   Both correspondences hold:
--   $$
--   f_S\text{ is positive}\ \Longleftrightarrow\ \rho^{T_S}\text{ is block-positive across }1|23,
--   $$
--   $$
--   g_S\text{ is positive}\ \Longleftrightarrow\ \rho^{T_S}\text{ is block-positive across }1|2|3.
--   $$
--   Positivity means PSD output on every PSD input, without input trace normalization. For the first equivalence, the output sites $23$ form one unrestricted block; for the second they are tested separately. The partial trace is unnormalized and complex trace nonnegativity includes a zero imaginary part.
--
--   These equivalences translate exactly between the two specified map-positivity questions and their distinct block partitions.
-- source:
--   Positive maps from the walled Brauer algebra, arXiv:2112.12738v3, PDF p. 6, Proposition 4, Eqs.(29)-(33); Table I caption

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P12

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P12

attribute [local instance] Classical.propDecidable

/-- Proposition 4, PDF p.6, Eqs.(29)-(33) on pp.5-6, and Table I caption p.13.
Both equivalences are retained. For g_S the partition is 1|2|3, as its proof
and the table specify. S is proper but can be empty. -/
theorem tripartite_positivity_iff
    (d : ℕ) (hd : 0 < d) (rho : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) (hrho : WernerDensity rho)
    (S : Finset (Fin 3)) (hS : S ≠ Finset.univ) :
    (PositiveMap (productInputContraction (r := 1) (m := 2) (transposeRegisterSet S rho)) ↔
      InputOutputBlockPositive (r := 1) (m := 2) (transposeRegisterSet S rho)) ∧
    (PositiveMap (productInputContraction (r := 2) (m := 1) (transposeRegisterSet S rho)) ↔
      InputOutputBlockPositive (r := 2) (m := 1) (transposeRegisterSet S rho)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P12

end
