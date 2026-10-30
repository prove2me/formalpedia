-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_symmetric_bob_marginal
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.symmetric_bob_marginal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:20:25.424601+00:00
-- url     : https://prove2.me/theorems/ac593b60-a9e9-4b10-a047-3ed181b312af
-- title:
--   Lemma 3.2: symmetric Bob marginal without worse performance
-- statement:
--   For every deterministic PBT protocol with integers $d,N\ge1$ and any finite Alice space, there exists a replacement protocol with the same $d,N$, possibly a larger finite Alice space, whose Bob marginal $\rho'_B$ satisfies
--   $$U^{\otimes N}\rho'_B(U^{\otimes N})^\dagger=\rho'_B,\qquad P_\pi\rho'_BP_\pi^\dagger=\rho'_B$$
--   for all $U\in U(d)$ and port permutations $\pi$. Its squared entanglement fidelity is at least the original fidelity, and its full diamond error is at most the original error. More generally, every real convex channel cost invariant under simultaneous unitary input/output conjugation is no larger. This is the Bob-marginal symmetry reduction with Alice's flags retained.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 14, Lemma 3.2: symmetric Bob marginal without worse performance

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Lemma 3.2, PDF p.14, with the convex invariant-cost extension stated there.
The replacement may enlarge Alice's space by finite classical flags (proof p.15). -/
theorem symmetric_bob_marginal {d N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N)
    {A : Type*} [Fintype A] [DecidableEq A] (P : PBTProtocol d N A) :
    ∃ m : ℕ, ∃ Q : PBTProtocol d N (Fin m),
      BobSymmetric (traceLeft Q.resource) ∧ NoWorse Q.channel P.channel := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
