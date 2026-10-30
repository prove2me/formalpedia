-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_fano_holevo_converse
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.fano_holevo_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:53:27.107355+00:00
-- url     : https://prove2.me/theorems/9002e190-b5a1-477a-b5a4-598daea98ff2
-- title:
--   Fano and Holevo coding converse inequalities
-- statement:
--   For a positive-size code with uniform sent message $M$, normalized stochastic encoder, normalized decoder POVM, and normalized Bob cq outputs, let $e$ be its average error, $m$ its message count and $H_c=H(M\mid\widehat M)$ computed from the actual joint law $p(i,j)=\operatorname{Tr}(D_j W_B\circ\Gamma_i)/m$. Then $H_c\le h(e)+e\log m$ and $(1-e)\log m-h(e)\le\log m-H_c\le I_{mix}(W_B\circ\Gamma)$, where $h$ is binary entropy in nats. This includes $m=1$ and $e=0,1$; it uses the source\'s weaker $\log m$ version of Fano.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 19, Cited p.18–19: Fano/Holevo converse inequalities

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P23

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P56
  (IsLaw entropy average holevo uniform ProjectiveRep orbit productOutput)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch logNonnegativeExtended)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A Z B E : Type} [Fintype X] [Fintype A] [Fintype Z]
  [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- PDF pp.18–19: Fano and Holevo converse inequalities on actual codes. The
source's weaker log M version of Fano is retained, including M=1 and zero error. -/
theorem fano_holevo_converse [Nonempty X] [Nonempty B]
    (WB : X → Matrix B B ℂ) (hB : hayashiIsCQ WB) (M : ℕ) (C : WiretapCode X B M) :
    decodedConditionalEntropy WB C ≤ Real.binEntropy (hayashiCodeError WB C) +
      hayashiCodeError WB C * Real.log M ∧
    (1 - hayashiCodeError WB C) * Real.log M - Real.binEntropy (hayashiCodeError WB C) ≤
      Real.log M - decodedConditionalEntropy WB C ∧
    Real.log M - decodedConditionalEntropy WB C ≤ Imix (hayashiCompose WB C.encoder) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
