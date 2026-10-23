-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P11_cycleIrreversibility
-- name    : QAlgorithms.Papers.Independent.Gap20.P11.cycleIrreversibility
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:16:45.865819+00:00
-- url     : https://prove2.me/theorems/7d5b7e85-814e-4684-84b9-4e8015af0766
-- title:
--   The split-and-merge cycle has signed rate I(A:R)
-- statement:
--   Let $|\psi\rangle_{RAB}$ be a normalized pure state on finite, nonzero-dimensional complex registers. Write $S$ for von Neumann entropy in bits and $I(A:R)=S(A)+S(R)-S(AR)$. In the specified cycle, Bob first distributes Alice's share at rate $S(A)$, and Alice subsequently merges it back at signed rate $S(A\mid B)$. These rates satisfy
--
--   $$
--   S(A)+S(A\mid B)=I(A:R).
--   $$
--
--   This identity describes the irreversibility assigned to that cycle. A negative merging term accounts for entanglement production; the sum is a signed resource balance, and is not an assertion about the number of physical channel uses when that term is negative.
-- source:
--   Quantum information can be negative, arXiv:quant-ph/0505062v1, PDF p. 4, Unnumbered observation: irreversibility of the split-and-merge cycle

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P11

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, split-and-merge cycle: this is the signed rate identity for the
specified cycle, including negative merging cost, not a count of physical
channel uses or an optimality claim over all possible cycles. -/
theorem cycleIrreversibility {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi) :
    vnEntropy (traceRight (traceLeft (pureDensity psi))) +
      conditionalEntropy (traceLeft (pureDensity psi)) = referenceInformation psi := by sorry

end QAlgorithms.Papers.Independent.Gap20.P11

end
