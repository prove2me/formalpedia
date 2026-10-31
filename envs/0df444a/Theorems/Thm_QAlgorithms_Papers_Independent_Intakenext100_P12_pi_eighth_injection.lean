-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_pi_eighth_injection
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.pi_eighth_injection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:12:37.810986+00:00
-- url     : https://prove2.me/theorems/6f210e25-98df-4128-83f9-dc6f655873df
-- title:
--   §XI.A (112)–(116), Fig.5: H eigenstate and pi/8 injection
-- statement:
--   Let $|h_+\rangle=\cos(\pi/8)|0\rangle+\sin(\pi/8)|1\rangle$, $P=\operatorname{diag}(1,i)$, and $S=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$. Then $H|h_+\rangle=|h_+\rangle$ and $HP^{-1}|h_+\rangle=|A\rangle$, where $|A\rangle=(e^{-i\pi/8}|0\rangle+e^{i\pi/8}|1\rangle)/\sqrt2$. For every normalized data qubit $|\psi\rangle$, CNOT from data to $|A\rangle$ and target computational measurement give
--
--   $$\psi_0=\frac1{\sqrt2}S\psi,\qquad\psi_1=\frac1{\sqrt2}S^{-1}\psi,\qquad P\psi_1=\frac{e^{i\pi/4}}{\sqrt2}S\psi.$$
--
--   Both outcomes have probability $1/2$. This follows the displayed state, gate and Fig.5; the source's prose reverses the two conditional states. The correction is disclosed for independent moderation.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 15, §XI.A (112)–(116), Fig.5: H eigenstate and pi/8 injection

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section XI.A (112)–(116), Fig.5, PDF p.15: H-state conversion and pi/8 injection.
SOURCE CORRECTION: the printed prose reverses the outcomes. With (114),(115) and Fig.5,
outcome 0 gives S, outcome 1 gives S inverse; applying P in branch 1 fixes it up to exp(i*pi/4). -/
theorem pi_eighth_injection (psi : Bool → ℂ) (hnorm : finiteInner psi psi = 1) :
    QAlgorithms.hadamard.mulVec hadamardPlus = hadamardPlus ∧
    (QAlgorithms.hadamard * star QAlgorithms.phaseS).mulVec hadamardPlus = magicState ∧
    magicBranch false psi = (fun b => paperS.mulVec psi b / (Real.sqrt 2 : ℂ)) ∧
    magicBranch true psi = (fun b => (star paperS).mulVec psi b / (Real.sqrt 2 : ℂ)) ∧
    QAlgorithms.phaseS.mulVec (magicBranch true psi) =
      (fun b => cisPhase (Real.pi / 4) * paperS.mulVec psi b / (Real.sqrt 2 : ℂ)) ∧
    (∀ outcome : Bool, ∑ b, ‖magicBranch outcome psi b‖ ^ 2 = (1 : ℝ) / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
