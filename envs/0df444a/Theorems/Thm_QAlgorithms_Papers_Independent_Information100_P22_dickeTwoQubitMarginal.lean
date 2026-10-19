-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_dickeTwoQubitMarginal
-- name    : QAlgorithms.Papers.Independent.Information100.P22.dickeTwoQubitMarginal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:15:26.279908+00:00
-- url     : https://prove2.me/theorems/5873a70c-9947-4bda-bf58-54bb62f6267f
-- title:
--   Eq.(S70), unnumbered: exact Dicke two-qubit marginal
-- statement:
--   Let $n=2mk$, $m\ge2$, $k\ge1$, $0\le r\le n$, and choose any two distinct qubits of the normalized Dicke state. Their ordered computational marginal is
--   $$\rho_2=\frac{(n-r)(n-r-1)}{n(n-1)}|00\rangle\langle00|+\frac{r(r-1)}{n(n-1)}|11\rangle\langle11|+\frac{r(n-r)}{n(n-1)}(|01\rangle+|10\rangle)(\langle01|+\langle10|).$$
--   For $0<r<n$ its 01/10 coherence is nonzero. At $r=0,n$ it is respectively the pure 00 or 11 product density. It is never $I_4/4$. This is the structural two-qubit obstruction used against Dicke resources.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 43, Eq.(S70), unnumbered: exact Dicke two-qubit marginal

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Eq.(S70), PDF p.43: full formula, interior coherence, product endpoints, and nonuniformity. -/
theorem dickeTwoQubitMarginal (m k r : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hr : r ≤ 2*(m*k)) (a b : Fin (2*(m*k))) (hab : a ≠ b) :
    twoQubitMarginal (pureDensity (dicke (I := Fin (2*(m*k))) r)) a b = dickePairFormula (2*(m*k)) r ∧
    (0 < r → r < 2*(m*k) → (dickePairFormula (2*(m*k)) r) (false,true) (true,false) ≠ 0) ∧
    (r = 0 → dickePairFormula (2*(m*k)) r = pureDensity (ket (false,false))) ∧
    (r = 2*(m*k) → dickePairFormula (2*(m*k)) r = pureDensity (ket (true,true))) ∧
    dickePairFormula (2*(m*k)) r ≠ mixed (Bool × Bool) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
