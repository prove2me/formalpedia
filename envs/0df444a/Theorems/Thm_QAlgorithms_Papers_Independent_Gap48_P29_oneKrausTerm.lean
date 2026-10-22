-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_oneKrausTerm
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.oneKrausTerm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:11:43.238055+00:00
-- url     : https://prove2.me/theorems/17ed2d26-cdde-4940-b067-4e02b003277e
-- title:
--   A single Kraus term carries the entanglement fidelity
-- statement:
--   Let $\rho$ be a density operator on a nonzero finite-dimensional complex Hilbert space and $\mathcal A$ a completely positive trace-nonincreasing operation on that space. There is a finite nonempty Kraus representation $\mathcal A(X)=\sum_a A_aXA_a^\dagger$, allowed to depend on $\rho$, with a distinguished term $A_1$ such that
--
--   $$F_e(\rho,\mathcal A)=|\operatorname{tr}(A_1\rho)|^2.$$
--
--   Zero maps and zero fidelities are included by padding the representation with a zero operator. The formula concentrates fidelity, not the entire operation, into one term.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 4, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.4, Lemma 2: the operation is CP trace nonincreasing (p.2, Eq.(2)).
The decomposition may depend on rho; zero operations are
included by a padded zero Kraus term, so there is always a distinguished term. -/
theorem oneKrausTerm {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (A : Superop I I)
    (hA : TraceNonincreasingCPMap A) :
    ∃ m : ℕ, ∃ K : Fin (m + 1) → Matrix I I ℂ,
      Represents K A ∧ fe rho A = operatorFe rho (K 0) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
