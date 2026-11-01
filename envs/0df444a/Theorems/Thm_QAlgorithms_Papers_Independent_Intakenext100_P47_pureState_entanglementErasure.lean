-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P47_pureState_entanglementErasure
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P47.pureState_entanglementErasure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:21:09.244104+00:00
-- url     : https://prove2.me/theorems/4d4d6aea-8327-4e7e-a1ec-2773e2fc746c
-- title:
--   Section III.C: pure-state optimistic and pessimistic entanglement erasure
-- statement:
--   Let $|\psi\rangle\in A\otimes B$ be a normalized pure state on finite nonzero spaces, and let $\psi=|\psi\rangle\langle\psi|$. For $n\ge1$ and $\epsilon>0$, define $N(n,\epsilon)$ as the least number of product-unitary terms in a COLUR ensemble whose output on $\psi^{\otimes n}$ is within full trace norm $\epsilon$ of a normalized separable state. The feasible sizes are nonempty and their minimum is attained. The normalized logarithmic cost sequences and their outer error suprema are bounded. Define the optimistic and pessimistic entanglement-erasure rates using $\liminf$ and $\limsup$, respectively, followed by the supremum over $\epsilon>0$. Then
--
--   $$\underline E_{\rm er}(\psi)=E_{\rm er}(\psi)=S(\psi_A),\qquad C_{\rm er}(\psi)=2S(\psi_A).$$
--
--   This is the unconditional pure-state erasure theorem, including product states. The conjectured optimum for retained classical correlations is not used.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, PDF p. 8, Section III.C: pure-state optimistic and pessimistic entanglement erasure

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P47

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies localProduct)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon Config)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, III.C: unconditional pure-state erasure; no conjectural classical optimum is included. -/
theorem pureState_entanglementErasure {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (psi : EuclideanSpace ℂ (A × B)) (hpsi : IsState psi) :
    (∀ eps > (0 : ℝ), ∀ n, 0 < n →
      (disentanglingSizes (pureDensity psi) n eps).Nonempty ∧
      minimumDisentanglingSize (pureDensity psi) n eps ∈
        disentanglingSizes (pureDensity psi) n eps) ∧
    (∀ eps > (0 : ℝ), BddBelow (Set.range (entanglementBlockRate (pureDensity psi) eps)) ∧
      BddAbove (Set.range (entanglementBlockRate (pureDensity psi) eps))) ∧
    (∀ pessimistic,
      BddAbove {v | ∃ eps > (0 : ℝ),
        v = rateLimit pessimistic (entanglementBlockRate (pureDensity psi) eps)} ∧
      entanglementErasure (pureDensity psi) pessimistic =
        vnEntropy (traceRight (pureDensity psi))) ∧
    totalErasure (pureDensity psi) .coordinated .size true =
      2 * vnEntropy (traceRight (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P47

end
