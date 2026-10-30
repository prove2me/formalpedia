-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_group_bit_phase
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.group_bit_phase
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:32:13.485989+00:00
-- url     : https://prove2.me/theorems/fe396b9e-91ef-454b-b524-4d50f627e7ec
-- title:
--   Unnumbered finite-group bit-/phase-flip codes, Eqs.(60)–(64)
-- statement:
--   Let $G$ be any finite group with orthonormal basis $|g\rangle$. The normalized three-site encodings are $$V_b|g\rangle=|g,g,g\rangle,\qquad V_p|g\rangle=|G|^{-1}\sum_{h_1h_2h_3=g}|h_1,h_2,h_3\rangle.$$ The bit code exactly corrects the span of single-site left shifts; the phase code exactly corrects the span of single-site diagonal errors. Both obey the source’s left and right logical covariance rules: bit-code multipliers act on all sites, while phase-code left and right multipliers act on the first and last site respectively. Right multipliers are parametrized by inverses to respect group composition. Exact correction is expressed by the Knill–Laflamme criterion for these specified families.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 17, Unnumbered finite-group bit-/phase-flip codes, Eqs.(60)–(64)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF pp.17–18, (60)–(64): the named shift/diagonal families, plus the explicit
left and right transversal logical actions. Right action is parametrized by inverses. -/
theorem group_bit_phase (G : Type*) [Group G] [Fintype G] :
    (bitEncoding G)ᴴ * bitEncoding G = 1 ∧
    (groupPhaseEncoding G)ᴴ * groupPhaseEncoding G = 1 ∧
    CorrectsOperators (bitEncoding G) (fun e : Fin 3 × G => shiftError e.1 e.2) ∧
    CorrectsOperators (groupPhaseEncoding G) (fun e : Fin 3 × (G → ℂ) => diagonalError e.1 e.2) ∧
    (∀ g : G,
      basisMapMatrix (fun y : Fin 3 → G => fun i => g * y i) * bitEncoding G =
        bitEncoding G * basisMapMatrix (fun h => g * h)) ∧
    (∀ g : G, shiftError 0 g * groupPhaseEncoding G =
      groupPhaseEncoding G * basisMapMatrix (fun h => g * h)) ∧
    (∀ g : G,
      basisMapMatrix (fun y : Fin 3 → G => fun i => y i * g⁻¹) * bitEncoding G =
        bitEncoding G * basisMapMatrix (fun h => h * g⁻¹)) ∧
    (∀ g : G,
      basisMapMatrix (fun y : Fin 3 → G => Function.update y 2 (y 2 * g⁻¹)) * groupPhaseEncoding G =
        groupPhaseEncoding G * basisMapMatrix (fun h => h * g⁻¹)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
