-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P11_lemma_2_3
-- name    : QAlgorithms.Papers.Independent.Gap48.P11.lemma_2_3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:30:48.143277+00:00
-- url     : https://prove2.me/theorems/2a287f3b-f1ab-471b-a55f-691a9a870261
-- title:
--   Lemma 2.3: event decomposition of the Markov reconstruction
-- statement:
--   Let $\rho_{XYE}$ be a normalized positive density operator with finite nonempty classical registers $X,Y$ and a finite quantum register $E$. Let $\mathcal E$ be an event determined by $Y$: for each $y$, its occurrence is either certain or impossible. Write $\rho_{X\leftrightarrow Y\leftrightarrow E}$ for the reconstruction using $P_{XY}$ and the actual conditional quantum marginals $\rho_{E\mid Y=y}$. Then
--
--   $$
--   \rho_{X\leftrightarrow Y\leftrightarrow E}
--   =\Pr[\mathcal E]\,\rho_{X\leftrightarrow Y\leftrightarrow E\mid\mathcal E}
--   +\Pr[\mathcal E^{\mathrm c}]\,\rho_{X\leftrightarrow Y\leftrightarrow E\mid\mathcal E^{\mathrm c}}.
--   $$
--
--   Each conditional reconstruction is formed from the corresponding conditioned state. Neither event is required to have positive probability: a conditional version on an impossible event is arbitrary and has zero coefficient. This decomposition separates deterministic transcript events without changing the reconstruction.
-- source:
--   Composing Quantum Protocols in a Classical Environment, arXiv:0804.1059v2, PDF p. 4, Lemma 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P11

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Lemma 2.3, PDF p.4; Appendix A.3, PDF p.19. The event is determined by Y.
The second event is the complement: its overbar is present in the printed PDF but
lost in the extracted text. Zero-probability branches are allowed. -/
theorem lemma_2_3
    {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]
    [Nonempty X] [Nonempty Y] [Nonempty E]
    (r : CQProbabilityBlocks (X × Y) E) (hr : IsNormalizedCQ r) (event : Y → Prop) :
    conditionalMarkovReconstruction r Prod.snd =
      (eventProb r (fun c => event c.2) : ℂ) •
        conditionalMarkovReconstruction (conditioned r (fun c => event c.2)) Prod.snd +
      (eventProb r (fun c => ¬ event c.2) : ℂ) •
        conditionalMarkovReconstruction (conditioned r (fun c => ¬ event c.2)) Prod.snd := by sorry

end QAlgorithms.Papers.Independent.Gap48.P11

end
