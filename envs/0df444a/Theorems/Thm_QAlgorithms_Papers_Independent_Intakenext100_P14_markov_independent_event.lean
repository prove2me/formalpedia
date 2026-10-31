-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P14_markov_independent_event
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P14.markov_independent_event
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:19:35.109338+00:00
-- url     : https://prove2.me/theorems/38139213-f54c-4753-bda7-ce3ede4e95dc
-- title:
--   Independent-event decomposition of Markov reconstruction
-- statement:
--   Let $X,Y$ be finite classical registers and $E$ a finite quantum register in a normalized classical–quantum state. Let $A$ be an event independent of the joint pair $(X,Y)$. Markov reconstruction replaces the conditional quantum state at $(x,y)$ by the actual state conditioned only on $y$, retaining the classical joint distribution. Then
--
--   $$\rho_{X\leftrightarrow Y\leftrightarrow E}=\Pr[A]\,\rho_{X\leftrightarrow Y\leftrightarrow E\mid A}+\Pr[\bar A]\,\rho_{X\leftrightarrow Y\leftrightarrow E\mid\bar A}.$$
--
--   The identity includes events of probability zero or one: each right-hand term is represented by its weighted, unnormalized blocks, so a zero-weight branch contributes zero. This is precisely the independent-event clause of Lemma 2.1, and does not assert its invalid general clause.
-- source:
--   Secure Identification and QKD in the Bounded-Quantum-Storage Model, arXiv:0708.2557v3, PDF p. 6, Lemma2.1, valid independent-event clause

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P14

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Gap48.P11 (blockMatrix cqDistance)

open QAlgorithms.Papers.Independent.Claimed50.P31 (bb84Vector)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.6, Lemma 2.1 independent-event clause (Appendix A.1, p.21).
Event independence is with the joint pair (X,Y). The two right-hand terms are
weighted unnormalized reconstructions, preserving probability-zero/one events. -/
theorem markov_independent_event
    {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]
    (r : ((X × Y) × Bool) → Matrix E E ℂ)
    (hstate : QAlgorithms.IsDensityMatrix (blockMatrix r))
    (hindependent : ∀ xy,
      blockMass r (xy, true) =
        (∑ xy, blockMass r (xy, true)) * blockMass (cqPush r Prod.fst) xy) :
    markov (cqPush r Prod.fst) =
      markov (fun xy => r (xy, true)) + markov (fun xy => r (xy, false)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P14

end
