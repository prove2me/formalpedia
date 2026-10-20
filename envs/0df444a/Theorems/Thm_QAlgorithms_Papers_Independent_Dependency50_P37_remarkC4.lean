-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_remarkC4
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.remarkC4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:23:52.007997+00:00
-- url     : https://prove2.me/theorems/cf760cf8-f46e-456e-a26e-4949d9d23812
-- title:
--   Persistence of saturated left-multiplied Kraus-word spaces
-- statement:
--   Let $\Phi(X)=\sum_iK_iXK_i^*$ be a trace-preserving quantum channel on $M_d(\mathbb C)$, $d\ge1$. Let $S$ be its least nonzero invariant subspace and $P$ its orthogonal projector. Write $\mathcal K_n=\operatorname{span}\{K_{i_1}\cdots K_{i_n}\}$. For any $n\ge1$,
--
--   $$P\mathcal K_n=PM_d(\mathbb C)\quad\Longrightarrow\quad
--   P\mathcal K_m=PM_d(\mathbb C)\quad\text{for every }m\ge n.$$
--
--   Thus one saturated left Kraus-word span stays saturated. The projector is tied to the channel's invariant support, as in C.3.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 22, Remark C.4

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

/-- Remark C.4, PDF p.22: propagation of full left-multiplied Kraus span,
in the actual least invariant support context of C.3. -/
theorem remarkC4 {d p : ℕ} (hd : 0 < d) (K : Fin p → Operator d)
    (hK : IsKrausFamily K) (S : Submodule ℂ (EuclideanSpace ℂ (Fin d))) (P : Operator d)
    (hS : LeastInvariantSubspace (krausApply K) S) (hP : OrthogonalProjectorOnto P S)
    (n : ℕ) (hn : 0 < n)
    (hfull : leftMultiplySpace P (krausWordSpace K n) = leftMultiplySpace P ⊤) :
    ∀ m : ℕ, n ≤ m →
      leftMultiplySpace P (krausWordSpace K m) = leftMultiplySpace P ⊤ := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
