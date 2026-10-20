-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_noiselessEvaluation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.noiselessEvaluation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:42:42.513908+00:00
-- url     : https://prove2.me/theorems/168050ae-ecaf-4688-b7cf-665a66dcd90a
-- title:
--   Proposition 13: noiseless qudit evaluation, including d=1 correction
-- statement:
--   For every integer $d\ge1$, let $\mathcal I_d$ be the identity channel on a $d$-dimensional complex register. In bits per use,
--
--   $$C(\mathcal I_d)=C_\beta(\mathcal I_d)=C_\zeta(\mathcal I_d)=\log_2d,\qquad C_E(\mathcal I_d)=2\log_2d.$$
--
--   If $d\ge2$, then $\log_2d<2\log_2d$. At $d=1$ all four capacities vanish. The printed strict inequality omitted the nontrivial-dimension restriction; the equalities remain valid at dimension one. This correction preserves the noiseless evaluations and was independently verified in round 1.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 17, Proposition 13

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

/-- PDF p.17, Proposition 13, CORRECTED EDGE: all equalities include d=1,
where they equal zero. The printed strict inequality requires d≥2.
See HARD.md for printed/changed/why; independent moderation is pending. -/
theorem noiselessEvaluation (d : ℕ) (hd : 0 < d) :
    letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    ordinaryClassicalCapacity (id : Superop (Fin d) (Fin d)) = log2 d ∧
    cBeta (id : Superop (Fin d) (Fin d)) = log2 d ∧
    cZeta (id : Superop (Fin d) (Fin d)) = log2 d ∧
    eaCapacity (id : Superop (Fin d) (Fin d)) = 2 * log2 d ∧
    (2 ≤ d → log2 d < 2 * log2 d) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
