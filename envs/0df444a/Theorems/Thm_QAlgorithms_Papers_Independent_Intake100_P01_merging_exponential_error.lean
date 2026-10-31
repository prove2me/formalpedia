-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P01_merging_exponential_error
-- name    : QAlgorithms.Papers.Independent.Intake100.P01.merging_exponential_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:51:04.043196+00:00
-- url     : https://prove2.me/theorems/9d660c1c-9d41-4d2f-9ec4-e21357f57ae0
-- title:
--   Remark 5: exponential-error heuristic (with its rigorous Section IV.A resolution)
-- statement:
--   Fix a finite pure source $|\psi\rangle_{ABR}$ and a yield $0\le r<-S(A|B)$, where $S(A|B)=S(AB)-S(B)$ in bits. Put $\delta=(-S(A|B)-r)/3>0$ and $L_n=\lfloor2^{nr}\rfloor$. There exist source- and gap-dependent constants $c,C>0$ and $N$ such that every integer $n\ge N$, $n>0$, admits an LOCC merging protocol with no initial entanglement, output Schmidt rank $L_n$, and
--   $$\|\sigma_n-\Phi_{L_n}\otimes\psi_{B'BR}^{\otimes n}\|_1\le C\left(2^{-n\delta/4}+2^{-cn\delta^2/2}\right).$$
--   The output test retains the complete source and passive reference. This is the rigorous Section IV.A resolution of Remark 5's exponential-error heuristic; it includes $r=0$.
-- source:
--   Quantum state merging and negative information, arXiv:quant-ph/0512247v1, PDF p. 7, Remark 5: exponential-error heuristic (with its rigorous Section IV.A resolution)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P01

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply finTransport referenceInformation)

open QAlgorithms.Papers.Independent.Bridge50.P40
  (RankMergingCode OneWayMergingCode mergingFidelity SourceProtocolAchievable)

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRA marginalRB motherTarget motherOutput sourceCopies swap mutualInformation)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Advance50.P29 (weakTypicalProjector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.7,9, Remark 5 resolved by IV.A. Printed r<S(AB)-S(B) has the
wrong sign. Changed: 0<=r<S(B)-S(AB), as (35) requires. Integer floors
replace informal real Schmidt ranks. Constants may depend on source and gap. -/
theorem merging_exponential_error {A B R : Type}
    [Fintype A] [Fintype B] [Fintype R] [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi)
    (r : ℝ) (hr : 0 ≤ r)
    (hgap : r < -conditionalEntropy (traceLeft (pureDensity psi))) :
    let delta := (-conditionalEntropy (traceLeft (pureDensity psi)) - r) / 3
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      UnassistedMerging (sourceCopies n (pureDensity psi))
        (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * r)))
        (C * ((2 : ℝ) ^ (-(n : ℝ) * delta / 4) +
          (2 : ℝ) ^ (-c * (n : ℝ) * delta^2 / 2))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P01

end
