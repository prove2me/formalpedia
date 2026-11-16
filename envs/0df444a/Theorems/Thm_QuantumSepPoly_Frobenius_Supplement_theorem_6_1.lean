-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_Supplement_theorem_6_1
-- name    : QuantumSepPoly.Frobenius.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:57:15.535928+00:00
-- url     : https://prove2.me/theorems/1d07f63b-48ab-4064-9772-ea52f409d990
-- title:
--   Theorem 6.1 — Trace-distance SAT reduction in soft-exponential time
-- statement:
--   For every fixed real $\eta\in(0,1)$, there are a finite randomized RAM program, $C_\eta>0$ and $a_\eta\in\mathbb N$ chosen before every formula and random run. On every $n$-variable, $m$-clause 3-CNF, every run terminates within
--   $$2^{C_\eta\sqrt{n+m+2}\,[\log_2(n+m+2)]^{a_\eta}}$$
--   charged real-arithmetic operations, including explicit serialization of all complex matrix entries, and outputs an integer $d\ge1$ and a Hermitian positive-semidefinite trace-one matrix $\rho\in\mathcal L(\mathbb C^d\otimes\mathbb C^d)$. Its unconditional probabilities satisfy
--   $$f\text{ satisfiable}\ \Longrightarrow\ \Pr\{\rho\in\operatorname{Sep}(d,d)\}\ge9/10,$$
--   $$f\text{ unsatisfiable}\ \Longrightarrow\ \Pr\left\{\min_{\psi\in\operatorname{Sep}(d,d)}\frac12\|\rho-\psi\|_1>\eta\right\}\ge9/10.$$
--   The minimum is required to be attained. There is no bounded-occurrence input restriction, promise oracle, sampler-success condition, or assumed reduction contract. This is the trace-distance companion theorem, independent of the proof of the Frobenius goal.
--
--   Differences from the source:
--   - encoding: polynomial or soft-exponential arithmetic time → positive coefficient and natural exponent witnesses with L=n+m+2, before every input and random run; reason: this unpacks the source asymptotic orders uniformly and includes finite input/output serialization
--   - encoding: ordinary 3-CNF inputs and explicit density outputs → indexed three-literal clauses over Fin n, published CNF satisfaction, and a finite matrix-output port; reason: duplicate occurrences are preserved in the input; all source formulas and matrix entries remain represented
--   - encoding: the minimum of half the unnormalized trace norm → Gram-eigenvalue Schatten norm, separable infimum, and an attained minimizing state with the strict gap; reason: on positive-dimensional finite complex spaces this is the same trace-distance minimum
--   - generalization: 3-CNF with three literal slots per clause → clauses with at most three occurrences, including empty clauses; reason: three-slot inputs embed directly; nonempty short clauses can be padded by repetition, and empty clauses have an immediate unsatisfiable branch without changing the resource order
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Theorem 6.1, p. 24 (PDF p. 24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_CNF
import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_TraceGeometry

open scoped BigOperators ENNReal

namespace QuantumSepPoly.Frobenius.Supplement

theorem theorem_6_1 (η : ℝ) (hη : 0 < η ∧ η < 1) :
    ∃ (P : RAMProgram) (C : ℝ) (a : ℕ), 0 < C ∧
      ∀ n m (f : CNF3 n m),
        (∀ r, MatrixTerminates P (cnfInput f) (softExpBound C a n m) r ∧
          1 ≤ (ramResult P (cnfInput f) r).nat 0 ∧
          IsDensity (matrixOutput (ramResult P (cnfInput f) r))) ∧
        (Satisfiable f → ENNReal.ofReal (9/10 : ℝ) ≤ tapeLaw {r |
          matrixOutput (ramResult P (cnfInput f) r) ∈
            Sep ((ramResult P (cnfInput f) r).nat 0)}) ∧
        (¬ Satisfiable f → ENNReal.ofReal (9/10 : ℝ) ≤ tapeLaw {r |
          TraceGap η (matrixOutput (ramResult P (cnfInput f) r))}) := by sorry

end QuantumSepPoly.Frobenius.Supplement
