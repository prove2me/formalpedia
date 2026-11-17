-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_Supplement_theorem_1_5
-- name    : UnitaryQIPPSPACE.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:39:42.676052+00:00
-- url     : https://prove2.me/theorems/37211fa8-5e4f-4e6d-a505-7699b4baccb3
-- title:
--   Theorem 1.5 — EFI pairs imply $\mathsf{BQP}\neq\mathsf{PSPACE}$
-- statement:
--   If EFI pairs exist (Definition 5.5), then
--   $$\mathsf{BQP}\neq\mathsf{PSPACE}.$$
--
--   An EFI pair is a pair of efficiently generated families of mixed states $\rho_{0,n},\rho_{1,n}$ that are statistically far ($\mathrm{TD}(\rho_{0,n},\rho_{1,n})\ge1/q(n)$ eventually, for a polynomial $q\ge1$) but computationally indistinguishable (every uniform quantum polynomial-time distinguisher, even with polynomial-size quantum advice, has negligible advantage). EFI pairs are a candidate minimal assumption for quantum cryptography; the theorem says that proving their existence would in particular separate $\mathsf{BQP}$ from $\mathsf{PSPACE}$, answering a question of Brakerski, Canetti and Qian.
--
--   **Formalization Note** $\mathsf{BQP}$ and $\mathsf{PSPACE}$ are the published unrelativized classes (sets of languages over $\{0,1\}$), taken at the empty oracle.
--
--   Differences from the source:
--   - reading: a uniform quantum polynomial-time algorithm G on input (1^n, b) → UniformGen: circuits G n b of the base model from 0 to k(n) qubits, size ≤ p(n), described by one Turing machine from (1^n, b) within p(n) steps; reason: the paper's circuit model (§2, p.10) with the time-uniformity convention of Definition 2.6; measurement and partial trace allowed, so mixed outputs are allowed
--   - reading: quantum polynomial-time distinguisher D with polynomial-size quantum advice {σ_n} → Distinguisher.IsQPT: a uniform family of base circuits on k(n) + a(n) qubits (a(n) ≤ p(n)), described from 1^n in p(n) steps, output qubit 0 measured; σ_n any density matrix on a(n) qubits; reason: uniform QPT algorithm receiving 1^n and the advice state, as the definition is worded; the advice may be any (mixed) state
--   - encoding: ν negligible: ν(n) < 1/p(n) eventually for every positive polynomial p → published QAdvFew.PoQOracle.Negligible: ν ≥ 0 and ∀ c > 0, eventually ν(n) ≤ n^(−c); reason: equivalent for nonnegative ν, and the advantage is an absolute value
--   - encoding: a polynomial q ≥ 1 → q ∈ ℕ[X] with q(n) ≥ 1 for every n; reason: a real polynomial q ≥ 1 on ℕ is dominated by one with natural coefficients, which only lowers 1/q
--   - encoding: a pair of mixed states ρ_{0,n}, ρ_{1,n} → genState k G n b on the same k(n) qubits for b = false, true; reason: the trace distance of (F) compares states on one space; b = 0 is false
--   - reading: BQP ≠ PSPACE (classes not defined in the paper) → QAdvFew.PoQOracle.BQP noOracle ≠ QAdvFew.PoQOracle.PSPACE noOracle; reason: the standard classes, as published (uniform polynomial-size Clifford+T circuit families with bounds 2/3, 1/3; polynomial-space Turing machines), with the empty oracle
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Theorem 1.5, p.4 (PDF p.6), restated p.43 (PDF p.45); proof pp.43–44 (PDF pp.45–46)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_BQP
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_UnitaryQIPPSPACE_SpaceUniform
import Definitions.Def_UnitaryQIPPSPACE_Supplement_IsEFIPair

namespace UnitaryQIPPSPACE

namespace Supplement

/-- **Theorem 1.5** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held version
sha256 9e357a00…, p. 4 (PDF p. 6), restated p. 43 (PDF p. 45)): "If EFI pairs exist, then
`BQP ≠ PSPACE`."

**Formalization Note** EFI pairs are Definition 5.5 (`EFIPairsExist`). `BQP` and `PSPACE` are the
published classes `QAdvFew.PoQOracle.BQP` and `QAdvFew.PoQOracle.PSPACE` at the empty oracle
`noOracle`, both sets of languages over `{0, 1}`. -/
theorem theorem_1_5 (h : EFIPairsExist) :
    QAdvFew.PoQOracle.BQP noOracle ≠ QAdvFew.PoQOracle.PSPACE noOracle := by sorry

end Supplement

end UnitaryQIPPSPACE
