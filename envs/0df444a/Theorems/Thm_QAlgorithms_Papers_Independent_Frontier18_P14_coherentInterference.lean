-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P14_coherentInterference
-- name    : QAlgorithms.Papers.Independent.Frontier18.P14.coherentInterference
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:05:22.665983+00:00
-- url     : https://prove2.me/theorems/ee3ecd5d-5d0d-4276-8048-9d361bd898ef
-- title:
--   Coherent inputs remain product coherent outputs
-- statement:
--   For all complex $a,b$, let $|a,b\rangle=|a\rangle\otimes|b\rangle$ have occupation coefficients $e^{-(|a|^2+|b|^2)/2}a^mb^n/\sqrt{m!n!}$. These coefficients are square summable and the resulting vector has norm one. For every unitary two-mode beam matrix,
--
--   $$V_B|a,b\rangle=|B_{11}a+B_{12}b,\,B_{21}a+B_{22}b\rangle.$$
--
--   Thus the outgoing modes are uncorrelated coherent states. For the real balanced matrix (4.23), equal input amplitudes give $|\sqrt2 a,0\rangle$, and opposite input amplitudes give $|0,-\sqrt2 a\rangle$. Vacuum is fixed, so these are exact vector identities. The unspecified uniqueness claim is not part of this pinned result.
-- source:
--   Quantum Physics of Simple Optical Instruments, arXiv:quant-ph/0305007v2, PDF p. 21, §4.3: coherent inputs remain uncorrelated coherent outputs

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet)

/-- PDF pp.20–22, (4.13)–(4.16),(4.23): normalized coherent products
remain exact coherent products, with vacuum phase fixed. Includes both balanced
constructive/destructive interference cases. The separately ambiguous uniqueness
sentence is not asserted. -/
theorem coherentInterference :
    (∀ a b : ℂ, Memℓp (coherentPairCoefficients a b) 2 ∧
      ‖coherentPair a b‖ = 1 ∧
      ∀ mn, coherentPair a b mn = coherentCoefficient a mn.1 * coherentCoefficient b mn.2) ∧
    (∀ (B : Matrix (Fin 2) (Fin 2) ℂ),
      B ∈ Matrix.unitaryGroup (Fin 2) ℂ → ∀ a b : ℂ,
      passiveApply B (coherentPair a b) =
        coherentPair (B 0 0 * a + B 0 1 * b) (B 1 0 * a + B 1 1 * b)) ∧
    (∀ a : ℂ,
      passiveApply balanced (coherentPair a a) = coherentPair ((Real.sqrt 2 : ℂ) * a) 0 ∧
      passiveApply balanced (coherentPair a (-a)) = coherentPair 0 (-(Real.sqrt 2 : ℂ) * a)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P14

end
