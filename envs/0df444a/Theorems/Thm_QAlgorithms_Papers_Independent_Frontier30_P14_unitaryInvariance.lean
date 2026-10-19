-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P14_unitaryInvariance
-- name    : QAlgorithms.Papers.Independent.Frontier30.P14.unitaryInvariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:18:46.574985+00:00
-- url     : https://prove2.me/theorems/f5656e09-fb12-43d7-8223-98a4ae6a00a9
-- title:
--   Unitary changes preserve both represented properties
-- statement:
--   Fix a joint unitary $U$, environmental density $\sigma$, and the resulting receiver/environment pair $(E,F)$. For carrier unitaries $R,V$, put $C_S(X)=SXS^\dagger$ and define $E'=C_V\circ E\circ C_R$, $F'=F\circ C_R$. Then
--
--   $$
--   \mathrm{WD}(E,F)\iff\mathrm{WD}(E',F'),\qquad
--   \mathrm{AD}(E,F)\iff\mathrm{AD}(E',F').
--   $$
--
--   Here WD and AD mean full-space CPTP recoverability in the environmental and receiver directions, respectively, on every input density. The environmental output uses the same input change. These are the two output legs of the transformed representation, so the result preserves both properties under unitary equivalence.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, PDF p. 2, §II, final sentence

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace QAlgorithms.Papers.Independent.Frontier30.P14

/-- Section II, PDF p.2: fixed input and dilationReceiver-output unitary changes preserve
both properties. The environmental output changes by the SAME input unitary;
these are the output legs of the correspondingly transformed representation. -/
theorem unitaryInvariance {I J : Type} [Nonempty I]
    (U : (Hilbert (I × J) ≃ₗᵢ[ℂ] Hilbert (I × J))) (sigma : State J) (R V : (Hilbert I ≃ₗᵢ[ℂ] Hilbert I)) :
    (WeaklyDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients) ↔
      WeaklyDegradable (boundedUnitaryConjugation V ∘ dilationReceiver U sigma.coefficients ∘ boundedUnitaryConjugation R)
        (weakComplement U sigma.coefficients ∘ boundedUnitaryConjugation R)) ∧
    (AntiDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients) ↔
      AntiDegradable (boundedUnitaryConjugation V ∘ dilationReceiver U sigma.coefficients ∘ boundedUnitaryConjugation R)
        (weakComplement U sigma.coefficients ∘ boundedUnitaryConjugation R)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P14

end
