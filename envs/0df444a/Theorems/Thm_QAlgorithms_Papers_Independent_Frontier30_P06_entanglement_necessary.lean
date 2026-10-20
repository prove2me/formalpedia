-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P06_entanglement_necessary
-- name    : QAlgorithms.Papers.Independent.Frontier30.P06.entanglement_necessary
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:28:08.240669+00:00
-- url     : https://prove2.me/theorems/f88e9dce-f04a-4682-877c-c15b19c0b030
-- title:
--   Entanglement is necessary to exceed the non-feedback bound
-- statement:
--   Consider any legal finite-dimensional executed classical-feedback protocol, with no initial shared entanglement, $n$ channel blocks $N_j$, an arbitrary normalized message prior $p$, and final receiver memory $B_{\mathrm f}$. Let $\rho_j$ and $\omega_j$ be its average total states immediately before and after the same inter-block LOCC feedback step $j$. Both include the untouched message reference, grouped with the receiver; the opposite side contains all retained sender systems. Then
--
--   $$
--   I(M:B_{\mathrm f})>\sum_{j=0}^{n-1}\chi(N_j)
--   \quad\Longrightarrow\quad
--   \exists j\ (j+1<n):\ \rho_j\text{ and }\omega_j\text{ are both entangled across this cut}.
--   $$
--
--   There is also the operational implication. Let $N$ be a fixed positive finite-dimensional memoryless channel, and consider any sequence of legal classical-feedback codes whose physical lengths tend to infinity, whose uniform-message average errors tend to zero, and whose eventual rates approach at least $R\ge0$ bits per use. If $R>C(N)$, where $C(N)$ is the unassisted operational capacity, then some code in that very sequence has an inter-block feedback step for which both average total states are entangled across the specified cut.
--
--   This is a necessary condition for exceeding the non-feedback bound, not a sufficient condition or a capacity advantage for every channel that is not entanglement-breaking.
-- source:
--   On Feedback and the Classical Capacity of a Noisy Quantum Channel, arXiv:quant-ph/0305176v1, PDF p. 4, III.C final paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Frontier30.P06

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (Backward tensorAction)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

/-- PDF p.4, III.C final paragraph: exceeding the finite non-feedback information
bound requires entanglement of the average TOTAL state on both sides of the SAME
LOCC feedback step. For every code sequence achieving a rate above operational C,
such a step must occur in that sequence. This is necessity, not sufficiency. -/
theorem entanglement_necessary :
    (∀ {ch : ℕ → Backward} {n M : ℕ} (P : FeedbackExecution ch n M), P.Valid →
      ∀ p : Fin M → ℝ, Prior p →
      (∑ j ∈ Finset.range n, channelHolevo (ch j).map) < P.information p →
      ∃ j, j+1 < n ∧
        ¬ Entanglement.IsSeparablePositive
          (cutState p (fun m => P.recordedSent m j)) ∧
        ¬ Entanglement.IsSeparablePositive (cutState p (fun m => P.recordedState m (j+1)))) ∧
    (∀ (N : Backward), ChannelValid N → ∀ (codes : ℕ → BlockCode N) (R : ℝ),
      Achieves (fun _ => True) codes R → unassistedCapacity N < ENNReal.ofReal R →
      ∃ k j, j+1 < (codes k).rounds ∧
        ¬ Entanglement.IsSeparablePositive
          (cutState (uniformPrior (codes k).messages)
            (fun m => (codes k).protocol.recordedSent m j)) ∧
        ¬ Entanglement.IsSeparablePositive
          (cutState (uniformPrior (codes k).messages)
            (fun m => (codes k).protocol.recordedState m (j+1)))) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P06

end
