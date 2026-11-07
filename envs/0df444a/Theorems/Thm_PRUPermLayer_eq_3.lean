-- Prove2me | Theorems.Thm_PRUPermLayer_eq_3
-- name    : PRUPermLayer.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:13.134925+00:00
-- url     : https://prove2.me/theorems/a2aceba3-eca8-4712-ba81-c923ad37b6b8
-- title:
--   Eq. (3) — $A_{\mathrm{Cl}} = (I+\mathrm{SWAP})/3$, $H_{\mathrm{Cl}} = I/2$, $\delta_{\mathrm{eq}} = 2/3$, $\lambda_+ = 1/2$
-- statement:
--   For the uniform distribution $\mu_{\mathrm{Cl}}$ on the 24 single-qubit Clifford gates,
--   $$
--   A_{\mathrm{Cl}} = \frac{I + \mathrm{SWAP}}{3}, \qquad H_{\mathrm{Cl}} = \frac{I}{2}, \qquad \delta_{\mathrm{eq}} = \frac23, \qquad \lambda_+ = \frac12 .
--   $$
--
--   These two numbers are all of the single-qubit law that the security of $PL$ depends on; they give the base $2/3$ of Theorem 1.1. All four clauses are stated.
--
--   Differences from the source:
--   - encoding: the uniform distribution on the 24 Clifford gates modulo global phase → the uniform distribution on 24 fixed representatives; reason: a phase on $C$ cancels in $(C\otimes C)^\dagger \pi_{\mathrm{eq}}(C\otimes C)$ and in $C^\dagger|+\rangle\langle+|C$; same operators
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.4, Eq. (3), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_PRUPermLayer_cliffordLaw
import Definitions.Def_PRUPermLayer_collisionOp
import Definitions.Def_PRUPermLayer_plusOp
import Definitions.Def_PRUPermLayer_deltaEq
import Definitions.Def_PRUPermLayer_lambdaPlus
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Eq. (3)** (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.4, display (3), p.11 (PDF p.13)). For the uniform distribution on the 24
single-qubit Clifford gates, `A_Cl = (I + SWAP)/3`, `H_Cl = I/2`, `δ_eq = 2/3`, `λ₊ = 1/2`.

**Formalization Note** `SWAP` is the published `QAlgorithms.swapGate` on `Bool × Bool`; the
Clifford law is `cliffordLaw` (one representative per phase class). -/
theorem eq_3 :
    collisionOp cliffordLaw = (1 / 3 : ℂ) • (1 + QAlgorithms.swapGate) ∧
      plusOp cliffordLaw = (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ) ∧
      deltaEq cliffordLaw = 2 / 3 ∧ lambdaPlus cliffordLaw = 1 / 2 := by sorry

end PRUPermLayer
