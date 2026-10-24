-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_arbitrary_state_preparation
-- name    : QAlgorithms.Papers.Independent.Support50.P42.arbitrary_state_preparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:22:00.562989+00:00
-- url     : https://prove2.me/theorems/5a8f34d5-81da-47e8-b7b7-399c1d5b1082
-- title:
--   Exact preparation from finitely many standard singlets
-- statement:
--   Let $\rho_{AB}$ be any positive semidefinite trace-one density on positive finite local dimensions $a,b$, including pure and mixed targets. Put $q=\lceil\log_2b\rceil$. There is an exact local protocol using $q$ shared singlets and at most $2q$ classical bits from Alice to Bob such that
--
--   $$\mathcal L\bigl((|\Psi^-\rangle\langle\Psi^-|)^{\otimes q}\bigr)=\rho_{AB}.$$
--
--   The classical bound is witnessed by a complete Alice instrument with at most $2^{2q}$ communicated outcomes and conditional Bob channels. When $b=2^r$, the direct resource count is $q=r$. This is a sufficient preparation method; it does not assert optimality.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 1, Abstract and §V: exact finite preparation of pure or mixed shared states

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- Abstract and PDF pp.15--17: exact finite preparation of pure or mixed
states. Printed on pp.15--16: log2 b singlets and 2 log2 b cbits. Changed:
choose the explicit qubit embedding q=ceil(log2 b), giving q singlets and at most
2q cbits. This makes the standard-singlet count integral for general b; for
b=2^q the direct count remains exactly q. This is a sufficient budget. -/
theorem arbitrary_state_preparation (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho) :
    (∃ L : Superop (Fin (2^(Nat.clog 2 b)) × Fin (2^(Nat.clog 2 b))) (Fin a × Fin b),
      FiniteLOCC L ∧ OneWayBits (2*Nat.clog 2 b) L ∧ L (singlets (Nat.clog 2 b))=rho) ∧
    (∀ q : ℕ, b=2^q → Nat.clog 2 b=q) := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
