-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_betaAdditivity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.betaAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:40:33.710298+00:00
-- url     : https://prove2.me/theorems/6a0cfd23-7dfc-442b-a6d7-760ea9beca5d
-- title:
--   Unnumbered remark: additivity of C_β
-- statement:
--   Let $\mathcal N:A\to B$ and $\mathcal G:C\to D$ be CPTP channels on nonzero finite complex registers, with arbitrary possibly different dimensions. Define $C_\beta=\log_2\beta$ using the four-inequality Choi program of Eq.(45). Then
--
--   $$C_\beta(\mathcal N\otimes\mathcal G)=C_\beta(\mathcal N)+C_\beta(\mathcal G).$$
--
--   The tensor product acts on all input operators, including entangled inputs. This is exact additivity of the bound, beyond the one-sided product estimate for success probabilities.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 16, Unnumbered remark

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF p.16, unnumbered remark: additivity, with arbitrary different dimensions. -/
theorem betaAdditivity [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (N : Superop A B) (hN : IsChannel N) (G : Superop C D) (hG : IsChannel G) :
    cBeta (tensorChannel N G) = cBeta N + cBeta G := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
