-- Prove2me | Theorems.Thm_QuantumParallelRepetition_conditioningCertificate_of_above_exponential
-- name    : QuantumParallelRepetition.conditioningCertificate_of_above_exponential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T05:56:53.02808+00:00
-- url     : https://prove2.me/theorems/97708abc-31b5-4a59-a499-5aa4d30ef63f
-- title:
--   Above-threshold repeated success yields a conditioning certificate
-- statement:
--   Let $G$ be a finite two-player game with nonempty answer sets $A,B$, let $n>0$, and put $\varepsilon=1-\omega^*(G)>0$. Fix $K\ge1$ and write
--   $$C=\operatorname{pdfRoundingCoefficient}(K),\qquad \ell=\log(|A||B|),\qquad d=\frac{\varepsilon^{13}}{8(4C)^{12}(\varepsilon+\ell)}.$$
--   Suppose a strategy $S$ for the repeated game wins with probability greater than $e^{-dn}$. Then there is a set $D$ of conditioned coordinates with a nonempty complement and positive postselection mass such that
--   $$\operatorname{failure}_D<\varepsilon/2,\qquad 0\le\eta_D<\left(\frac{\varepsilon}{4C}\right)^{12},\qquad \kappa_D\le\sqrt{3\eta_D/2}.$$
--   Here $\operatorname{failure}_D$ is the average failure probability of a uniformly chosen remaining coordinate after postselection, $\eta_D$ is the martingale information rate, and $\kappa_D$ is the source Pinsker rate, using the existing definitions in this development.
--
--   This is the conditioning stage of the exponential repetition proof. Its conclusion collects exactly the hypotheses needed by the subsequent rounding stage. It requires no quantum rounding assumption.
-- source:
--   Reorganization of the conditioning and rounding stages in OpenAI, ten-proofs, QuantumParallelRepetition.lean, commit 94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, pdf_distributionUniformExponential_of_uniform_source_rounding, lines 67765–67911: https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L67765-L67911 . Existing Prove2Me proof: https://prove2.me/submissions/f7cea14e-2b4d-4d58-988d-602c87bbeb52 . Also vendored in vidick/MIPRE-formalization, commit 70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed, MIPRE/Background/Repetition/TenProofs/QuantumParallelRepetition/Part08.lean, pdf_distributionUniformExponential_of_uniform_source_rounding. This statement packages part of the existing proof; it is not a new quantitative bound.

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_26

open QuantumParallelRepetition
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

theorem QuantumParallelRepetition.conditioningCertificate_of_above_exponential
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (K : ℝ) (constant : 1 ≤ K)
    (alice : Nonempty A) (bob : Nonempty B)
    (gap : 0 < 1 - entangledValue G) (length : 0 < n)
    (winning :
      Real.exp
        (-pdfGapRate (pdfRoundingCoefficient K) (1 - entangledValue G)
          (Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) * (n : ℝ)) <
        S.winProbability) :
    ∃ D : Finset (Fin n),
      0 < (Finset.univ \ D).card ∧
      0 < repeatedPostselectionMass G n S D ∧
      uniformRemainingFailure (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D < (1 - entangledValue G) / 2 ∧
      0 ≤ martingaleRate G n S D ∧
      martingaleRate G n S D <
        ((1 - entangledValue G) / (4 * pdfRoundingCoefficient K)) ^ (12 : ℕ) ∧
      exactSourcePinskerRate G n S D ≤
        Real.sqrt ((3 / 2 : ℝ) * martingaleRate G n S D) := by sorry
