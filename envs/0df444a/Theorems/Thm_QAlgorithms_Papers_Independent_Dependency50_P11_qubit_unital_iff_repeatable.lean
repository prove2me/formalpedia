-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P11_qubit_unital_iff_repeatable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P11.qubit_unital_iff_repeatable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:40:18.618742+00:00
-- url     : https://prove2.me/theorems/37f74e7b-1bbf-4501-89f4-4763179cf91f
-- title:
--   Qubit unitality is equivalent to finite-memory repeatability
-- statement:
--   Let $\mathcal E$ be a completely positive, trace-preserving linear map on qubit operators. Then
--
--   $$\mathcal E(I_2)=I_2\quad\Longleftrightarrow\quad\mathcal E\text{ has a finite-memory repeatable implementation}.$$
--
--   The implementation consists of one fixed unitary and a fixed normalized finite memory initializer, serving every individual use for every product-input history without reset. Output marginals must agree with $\mathcal E$, while outputs may be correlated.
--
--   The equivalence uses the cited random-unitary characterization of unital qubit channels and is confined to dimension two.
-- source:
--   Repeatable quantum memory channels, arXiv:0808.3851v1, PDF p. 4, Section IV

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- Section IV, PDF p.4: for qubit channels only, unitality is equivalent to
finite-memory all-horizon repeatability, using the cited qubit characterization [15]. -/
theorem qubit_unital_iff_repeatable (E : Superop (Fin 2) (Fin 2)) (hE : IsChannel E) :
    IsUnital E ↔ HasFiniteRepeatableImplementation E := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P11

end
