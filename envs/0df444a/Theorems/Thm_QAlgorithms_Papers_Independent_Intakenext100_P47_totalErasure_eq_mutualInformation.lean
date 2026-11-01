-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P47_totalErasure_eq_mutualInformation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P47.totalErasure_eq_mutualInformation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:10:27.813988+00:00
-- url     : https://prove2.me/theorems/79aa560d-ac1a-4e78-afac-196e3f08d1d6
-- title:
--   Theorem II.3: total correlation equals quantum mutual information (original seed)
-- statement:
--   Let $\rho_{AB}$ be any density matrix on finite nonzero complex spaces $A,B$. For $n\ge1$ and $\epsilon>0$, minimize each noise cost over ensembles of product unitaries whose output on $\rho^{\otimes n}$ is within full trace norm $\epsilon$ of a normalized product state. The allowed ensembles may be coordinated, independent across the parties, restricted to Alice, or restricted to Bob. The three costs are $\log_2N$, the Shannon entropy $H(p)$, and entropy exchange $S_e(R,\rho^{\otimes n})$. All finite minima exist and are bounded below; their normalized sequences are bounded above and below. Define $C^{\mathcal M,c,\ell}_{\rm er}(\rho)$ by applying $\ell=\liminf$ or $\limsup$ to the normalized minima and then taking the supremum over $\epsilon>0$. The outer sets are bounded above. For every choice of noise class $\mathcal M$, cost $c$, and block limit $\ell$,
--
--   $$C^{\mathcal M,c,\ell}_{\rm er}(\rho)=I(A:B)_\rho=S(\rho_A)+S(\rho_B)-S(\rho).$$
--
--   All entropies are in bits. This gives the operational meaning of total correlation and retains both displayed extreme equalities and the following robustness assertion.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, PDF p. 4, Theorem II.3: total correlation equals quantum mutual information (original seed)

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

/-- PDF p.4, Theorem II.3, displayed extremes and robustness paragraph.
The minima and bounds exclude totalized-real infimum/limit artifacts. -/
theorem totalErasure_eq_mutualInformation {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) :
    (∀ eps > (0 : ℝ), ∀ mode cost,
      (∀ n, 0 < n → (totalCosts rho n eps mode cost).Nonempty ∧
        BddBelow (totalCosts rho n eps mode cost) ∧
        sInf (totalCosts rho n eps mode cost) ∈ totalCosts rho n eps mode cost) ∧
      BddBelow (Set.range (totalBlockRate rho eps mode cost)) ∧
      BddAbove (Set.range (totalBlockRate rho eps mode cost))) ∧
    (∀ mode cost pessimistic,
      BddAbove {v | ∃ eps > (0 : ℝ),
        v = rateLimit pessimistic (totalBlockRate rho eps mode cost)} ∧
      totalErasure rho mode cost pessimistic = mutualInformation rho) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P47

end
