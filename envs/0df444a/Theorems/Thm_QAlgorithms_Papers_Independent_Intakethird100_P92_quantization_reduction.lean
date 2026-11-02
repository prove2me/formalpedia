-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P92_quantization_reduction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P92.quantization_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:28:09.327196+00:00
-- url     : https://prove2.me/theorems/86de6cb0-f2ff-4b6b-8178-f75b3c2c171a
-- title:
--   OS quantization commutes with fixed-vector reduction
-- statement:
--   Let $U$ be a reflection-positive strongly continuous unitary one-parameter group on $(E,E_+,\theta)$ and assume that $E_+$ is $U$-cyclic. Let $E_{\mathrm{fix}}$ consist of vectors fixed by all $U_t$, and let $\widehat E_{\mathrm{fix}}$ consist of vectors fixed by all positive-time operators of the computed OS semigroup. Then $E_{\mathrm{fix}}\subseteq E_0$, the canonical restriction $q|_{E_{\mathrm{fix}}}$ is a unitary isomorphism onto $\widehat E_{\mathrm{fix}}$, and
--   $$E_{\mathrm{fix}}=\bigcap_{t>0}U_tE_+.$$
--
--   The unitary map is the restriction of the actual quotient, and its surjectivity is a conclusion. Cyclicity excludes the counterexamples discussed in Example 3.10.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, PDF p. 11, Proposition 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- Proposition 3.8, PDF pp. 11--12. The canonical fixed-space map is unitary
onto the quantized fixed space, and the intersection identity is in the original
Hilbert space. Cyclicity of Eplus is essential. -/
theorem quantization_reduction [hHilbert : CompleteSpace E] (r : ReflectionData E) (U : ReflectionGroup r)
    (hCyclic : IsCyclic U.group r.plus) :
    unitaryFixedSubspace U.group ≤ timeZero r ∧
    (∃ J : unitaryFixedSubspace U.group ≃ₗᵢ[ℂ] quantizedFixed r U,
      ∀ v : unitaryFixedSubspace U.group, ∃ hv : (v : E) ∈ r.plus,
        (J v : OS r) = osQ r ⟨v, hv⟩) ∧
    unitaryFixedSubspace U.group =
      ⨅ t : {t : ℝ // 0 < t}, r.plus.map (U.group.op t.val).toLinearMap := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P92

end
