-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P33_Bob_single_copy_gain
-- name    : QAlgorithms.Papers.Independent.Advance50.P33.Bob_single_copy_gain
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:35:55.576649+00:00
-- url     : https://prove2.me/theorems/354e77d3-235d-484f-a0c8-2fbbb91d1a31
-- title:
--   Exact attained single-copy discrimination gain over all token POVMs
-- statement:
--   Assume honest Alice, equal prior probabilities for the committed bit, and $a\in\mathbb C\setminus\{0\}$. Let $\rho_b$ be the actual token density from Eq. (3), $H=\rho_0-\rho_1$, and $D=\|H\|_1/2$. Both densities are normalized trace-class operators. Bob may use any binary POVM $(I-E,E)$ on the entire oscillator Hilbert space, with $0\le E\le I$ and outcome $E$ interpreted as bit $1$. Its trace pairings converge absolutely, and
--   $$
--   \|H\|_1=\frac{2e^{-2|a|^2}}{1+e^{-4|a|^2}},\qquad
--   G_{\max}=\frac{D}{2}=\frac{e^{-2|a|^2}}{2(1+e^{-4|a|^2})},\qquad
--   p_{\rm guess}^{\max}=\frac12+G_{\max}.
--   $$
--   Every such POVM is bounded by the displayed optimum, and a POVM attaining it exists. This is an optimization over full-space measurements, not just measurements postulated to act on a two-dimensional space. The source's prose/caption conflation of trace distance with success probability is corrected using its Eq. (16).
-- source:
--   Quantum bit commitment under Gaussian constraints, arXiv:1105.2140v2, PDF p. 7, IV, Eqs.(15)–(16): exact single-copy maximum information gain

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P33

open Filter

open scoped BigOperators Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator BipartiteFock fockKet bipartiteKet coherentKet
   coherentCoefficient CoherentRealized displacement displacementMatrix
   DisplacementRealized HasFockMatrix operatorOfMatrix IsDensity IsTraceClass
   nuclearTraceNorm fockTrace)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.6--7, Eqs.(12),(15)--(16): exact trace norm and maximum equal-prior
information gain, with an attained optimum among ALL oscillator POVMs. Gain
is guessing probability minus 1/2; the prose/caption's probability conflation is
not used. Trace-class and absolute trace-product convergence are conclusions. -/
theorem Bob_single_copy_gain (a : ℂ) (ha : a ≠ 0) :
    CoherentRealized ∧
    (∀ b : Bool, IsDensity (tokenState a b)) ∧ IsTraceClass (tokenDifference a) ∧
    nuclearTraceNorm (tokenDifference a) = 2 * tokenEigenvalue a ∧
    bobGain a = Real.exp (-2 * Complex.normSq a) / (2 * (1 + Real.exp (-4 * Complex.normSq a))) ∧
    (∀ E : FockOperator, IsOscillatorEffect E →
      Summable (fun n : ℕ => ((1 - E).comp (tokenState a false)) (fockKet n) n) ∧
      Summable (fun n : ℕ => (E.comp (tokenState a true)) (fockKet n) n) ∧
      tokenGuessProbability a E ≤ 1 / 2 + bobGain a) ∧
    ∃ E : FockOperator, IsOscillatorEffect E ∧ tokenGuessProbability a E = 1 / 2 + bobGain a := by sorry

end QAlgorithms.Papers.Independent.Advance50.P33

end
