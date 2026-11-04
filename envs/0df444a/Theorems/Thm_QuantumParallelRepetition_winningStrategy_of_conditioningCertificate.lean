-- Prove2me | Theorems.Thm_QuantumParallelRepetition_winningStrategy_of_conditioningCertificate
-- name    : QuantumParallelRepetition.winningStrategy_of_conditioningCertificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T05:56:55.793723+00:00
-- url     : https://prove2.me/theorems/6f5a726b-8655-4195-b80b-16bf31f82fd1
-- title:
--   A conditioning certificate and local rounding yield a strategy above the game value
-- statement:
--   Let $G$ be a finite two-player game with gap $\varepsilon=1-\omega^*(G)>0$. Fix a repeated-game strategy $S$, a set $D$ of conditioned coordinates, and $K\ge1$. Assume that at least one coordinate remains, postselection has positive mass, and the conditioning data satisfy
--   $$\operatorname{failure}_D<\varepsilon/2,\qquad 0\le\eta_D<\left(\frac{\varepsilon}{4C}\right)^{12},\qquad \kappa_D\le\sqrt{3\eta_D/2},\quad C=\operatorname{pdfRoundingCoefficient}(K).$$
--   Assume also the source-rounding statement for this fixed $G,n,S,D$: for every $0<\alpha\le1$ and $\gamma>0$, there is a legal single-game strategy whose winning probability is at least
--   $$1-\varepsilon/2-\operatorname{totalSamplingLoss}(K,\alpha,\eta_D,\kappa_D+\gamma).$$
--   Then there is a legal strategy $R$ for $G$ with
--   $$\omega^*(G)<\Pr[R\text{ wins }G].$$
--   The conclusion is the contradiction witness used in the repetition proof: every legal strategy is bounded above by the supremum defining $\omega^*(G)$. The rounding hypothesis remains explicit; this lemma packages the choice of accuracy parameters and the numerical error estimate, rather than proving the rounding construction itself.
-- source:
--   Reorganization of the conditioning and rounding stages in OpenAI, ten-proofs, QuantumParallelRepetition.lean, commit 94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, pdf_distributionUniformExponential_of_uniform_source_rounding, lines 67765–67911: https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L67765-L67911 . Existing Prove2Me proof: https://prove2.me/submissions/f7cea14e-2b4d-4d58-988d-602c87bbeb52 . Also vendored in vidick/MIPRE-formalization, commit 70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part08.lean, pdf_distributionUniformExponential_of_uniform_source_rounding. This statement packages part of the existing proof; it is not a new quantitative bound.

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_26

open QuantumParallelRepetition
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

theorem QuantumParallelRepetition.winningStrategy_of_conditioningCertificate
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (K : ℝ) (constant : 1 ≤ K)
    (gap : 0 < 1 - entangledValue G)
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (failure :
      uniformRemainingFailure (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D < (1 - entangledValue G) / 2)
    (entropy : 0 ≤ martingaleRate G n S D)
    (small :
      martingaleRate G n S D <
        ((1 - entangledValue G) / (4 * pdfRoundingCoefficient K)) ^ (12 : ℕ))
    (pinsker :
      exactSourcePinskerRate G n S D ≤
        Real.sqrt ((3 / 2 : ℝ) * martingaleRate G n S D))
    (round :
      0 < (Finset.univ \ D).card →
      0 < repeatedPostselectionMass G n S D →
      ∀ (alpha gamma : ℝ),
        0 < alpha → alpha ≤ 1 → 0 < gamma →
        uniformRemainingFailure (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D < (1 - entangledValue G) / 2 →
        ∃ rounded : Strategy G,
          roundedWinningLowerBound (1 - entangledValue G) K alpha
            (martingaleRate G n S D) (exactSourcePinskerRate G n S D + gamma) ≤
            rounded.winProbability) :
    ∃ rounded : Strategy G, entangledValue G < rounded.winProbability := by sorry
