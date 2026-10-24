-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P44_transpose_not_square_root_optimal
-- name    : QAlgorithms.Papers.Independent.Support50.P44.transpose_not_square_root_optimal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-24T00:07:38.738253+00:00
-- url     : https://prove2.me/theorems/2689b7dd-7fe2-48bd-8e2b-52f39914b10a
-- title:
--   A mixed-state counterexample to square-root optimality of transpose recovery
-- statement:
--   On three qubits let $\rho=\tfrac12|000\rangle\langle000|+\tfrac18|1\rangle\langle1|_A\otimes I_{BC}$. Let $T$ be its transpose recovery map. Let $R$ measure $B$ in the computational basis, prepare $|00\rangle\langle00|$ on outcome $0$, and prepare the uniform mixture on $|01\rangle,|10\rangle,|11\rangle$ on outcome $1$. Both maps are CPTP, and
--
--   $$T(|0\rangle\langle0|)=\tfrac56|00\rangle\langle00|+\tfrac16|01\rangle\langle01|,\qquad T(|1\rangle\langle1|)=\tfrac12(|10\rangle\langle10|+|11\rangle\langle11|).$$
--
--   Writing $F_R=F(\rho,(\mathrm{id}_A\otimes R)(\rho_{AB}))$ and $F_T$ analogously, with root fidelity, one has
--
--   $$F_R>0.9829,\qquad\sqrt{F_T}<0.9696,\qquad F_R\le F(A;C\mid B)_\rho,\qquad\sqrt{F_T}<F(A;C\mid B)_\rho.$$
--
--   Here $F(A;C\mid B)_\rho$ is the supremum over all CPTP recovery channels. Thus the square-root optimum bound fails for mixed states. The definition of $R$ includes zero action on off-diagonal matrix units.
-- source:
--   Universal recovery map for approximate Markov chains, arXiv:1504.07251v3, PDF p. 28, Appendix F

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)

open Filter

open scoped ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A B C E G : Type*}

/-- PDF p.28, Appendix F, (169)–(171): the concrete mixed-state counterexample,
with both decimals. Rendered p.28 confirms 0.9829 bounds F itself, whereas 0.9696
bounds sqrt(F). The map R has been defined on off-diagonal inputs as well. -/
theorem transpose_not_square_root_optimal :
    IsDensityMatrix counterexampleState ∧ IsChannel counterexampleRecovery ∧
    IsChannel counterexampleTranspose ∧
    counterexampleTranspose (Matrix.single false false 1) =
      Matrix.diagonal (fun z => if z = (false,false) then (5/6 : ℂ)
        else if z = (false,true) then (1/6 : ℂ) else 0) ∧
    counterexampleTranspose (Matrix.single true true 1) =
      Matrix.diagonal (fun z => if z.1 then (1/2 : ℂ) else 0) ∧
    9829/10000 < rootFidelity counterexampleState
      (idTensorSuperop counterexampleRecovery (marginalAB counterexampleState)) ∧
    Real.sqrt (rootFidelity counterexampleState
      (idTensorSuperop counterexampleTranspose (marginalAB counterexampleState))) < 9696/10000 ∧
    rootFidelity counterexampleState
      (idTensorSuperop counterexampleRecovery (marginalAB counterexampleState)) ≤
        finiteRecoveryFidelity counterexampleState ∧
    Real.sqrt (rootFidelity counterexampleState
      (idTensorSuperop counterexampleTranspose (marginalAB counterexampleState))) <
        finiteRecoveryFidelity counterexampleState := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end
