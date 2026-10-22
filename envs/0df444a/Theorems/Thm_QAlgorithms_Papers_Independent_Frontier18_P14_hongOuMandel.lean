-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P14_hongOuMandel
-- name    : QAlgorithms.Papers.Independent.Frontier18.P14.hongOuMandel
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:06:52.281987+00:00
-- url     : https://prove2.me/theorems/7e4e1de3-f1ed-4c0b-bae9-20876dcf1d61
-- title:
--   Hong–Ou–Mandel output in the paper’s real convention
-- statement:
--   Let $B=2^{-1/2}\begin{pmatrix}1&1\\-1&1\end{pmatrix}$. For one photon in each matched input mode, the full passive transformation gives
--
--   $$V_B|1,1\rangle=\frac{|2,0\rangle-|0,2\rangle}{\sqrt2}.$$
--
--   This vector is normalized. Joint photon counting gives probability $1/2$ to each of $(2,0)$ and $(0,2)$ and zero to every other outcome, including coincidence $(1,1)$. The relative minus sign fixes the source's reflection convention.
-- source:
--   Quantum Physics of Simple Optical Instruments, arXiv:quant-ph/0305007v2, PDF p. 22, §4.3: Hong–Ou–Mandel output

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet)

/-- PDF pp.22–23, (4.23)–(4.24): the real-reflection Hong–Ou–Mandel
output with its relative minus sign and no coincidence counts. -/
theorem hongOuMandel :
    passiveApply balanced (fockKet 1 1) =
      (1 / (Real.sqrt 2 : ℂ)) • (fockKet 2 0 - fockKet 0 2) ∧
    ‖passiveApply balanced (fockKet 1 1)‖ = 1 ∧
    (∀ mn : ℕ × ℕ, Complex.normSq (passiveApply balanced (fockKet 1 1) mn) =
      if mn = (2, 0) ∨ mn = (0, 2) then (1 / 2 : ℝ) else 0) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P14

end
