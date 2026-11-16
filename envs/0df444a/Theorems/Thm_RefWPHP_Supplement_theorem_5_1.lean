-- Prove2me | Theorems.Thm_RefWPHP_Supplement_theorem_5_1
-- name    : RefWPHP.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:28:57.178959+00:00
-- url     : https://prove2.me/theorems/ddc57eea-21f9-4944-8e3e-05516c107f60
-- title:
--   Theorem 5.1 — under the WPHP Hypothesis, if PK$_d$ is automatable in polynomial time then CNF-SAT is decidable in time $2^{o(n)} \cdot (n+m)^{O(1)}$
-- statement:
--   Assume the WPHP Hypothesis (Hypothesis 1.4) and let $d \in \mathbb N$. If $\mathrm{PK}_d$ is automatable in polynomial time on CNF formulas, then CNF-SAT admits a deterministic algorithm running in time
--
--   $$
--   2^{o(n)} \cdot (n + m)^{O(1)},
--   $$
--
--   where $n$ is the number of variables and $m$ the number of clauses of the input formula.
--
--   Equivalently, under the hypothesis, $\mathrm{PK}_d$ is not automatable in polynomial time unless CNF-SAT can be solved in subexponential time in the number of variables; this extends the Atserias–Müller theorem for Resolution to every fixed depth of Frege.
--
--   **Formalization Note** The hypothesis is the argument `hW : WPHPHypothesis`. Automatability is `PKAutomatable d` and the algorithm is `CNFSATSubexp`; both use Mathlib's `Turing.FinTM2` machines and the input encoding `encodeCNF`.
--
--   Differences from the source:
--   - reading: PK_d is not automatable in polynomial time unless CNF-SAT admits a 2^{o(n)}·(n+m)^{O(1)} algorithm → PKAutomatable d → CNFSATSubexp; reason: "not A unless B" is "A implies B"
--   - encoding: Assume the WPHP Hypothesis (Hypothesis 1.4) → hypothesis hW : WPHPHypothesis; reason: "Assume" is an implication
--   - reading: an unspecified deterministic algorithm and time measure → Mathlib Turing.FinTM2 machines with input/output alphabets ≃ Bool, steps counted by Turing.TM2OutputsInTime; reason: the paper names no model; both polynomial-time automatability and the class 2^{o(n)}(n+m)^{O(1)} are invariant under the polynomial simulations between standard deterministic models
--   - encoding: |φ|, the input formula and the output refutation as strings → encodeCNF φ (unary n and literal codes) and encodeDeriv ρ (length between derivSize ρ and (n+5)·derivSize ρ + 1); reason: explicit prefix-free encodings polynomially related to any standard encoding; the class of the statements does not change
--   - encoding: automatable in time T(|φ| + size_P(φ)) with T a polynomial; refutation systems "analogous" (p.17) → on every unsatisfiable CNF input, output a PK_d-refutation of its cedents within p(|φ| + pkSize d φ) steps, p : Polynomial ℕ; satisfiable inputs unconstrained; reason: the definition of §2.1.4 for refutation systems
--   - encoding: time 2^{o(n)} · (n + m)^{O(1)} → 2^{f n} · (n + m + 2)^c for some f : ℕ → ℕ with f n / n → 0 and some c : ℕ, on every input; reason: a real f = o(n) can be rounded up; the + 2 costs a constant factor 2^{O(1)} when n + m ≥ 1
--   - encoding: size is the length of a binary string (p.15); "in size T" → derivSize, the symbol count plus one per line; size at most T; reason: the two sizes differ by at most a logarithmic factor in the number of variables, which every bound in the statement absorbs (base mission convention)
--   - encoding: CNF clauses (of φ, Ref_s(φ), PHP, ontoPHP) written with → and ⋁ → each clause is the cedent of its literals; reason: p.15 collects a CNF into a set of cedents; no instance changes (base mission convention)
--   - reading: binary ∧/∨-Intro used as "repeated ∧-introduction", Cut on φ₁ ∧ ⋯ ∧ φ_m, cedents as sequences → the base PKStep: n-ary ∧/∨-introduction, Atomic LEM, weakening to any list containing the premise, Cut on one formula and on a conjunction, hypotheses; dag-like lines; reason: the base mission's published calculus; ⊤ and ⊥ are formulas there and PK_0 is Resolution (p.15)
--   - encoding: the set Φ of cedents of the CNF φ (p.15) → cnfCedents φ: every ordering of the literals of each clause is a cedent of φ; reason: a clause is a set of literals and fixes no order; the orders differ by one weakening step, so PK_d-refutation sizes change by at most a constant factor
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), Theorem 5.1, p.39 (PDF p.41); automatability §2.1.4, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_RefWPHP_Supplement_WPHPHypothesis
import Definitions.Def_RefWPHP_Supplement_PKAutomatable
import Definitions.Def_RefWPHP_Supplement_CNFSATSubexp

namespace RefWPHP

namespace Supplement

/-- Theorem 5.1, p.39 (PDF 41), of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…): "Assume the WPHP Hypothesis
(Hypothesis 1.4). For every `d ∈ ℕ`, the proof system `PK_d` is not automatable in polynomial time on
CNF formulas unless CNF-SAT admits a deterministic algorithm running in time
`2^{o(n)} · (n + m)^{O(1)}` where `n` is the number of variables and `m` is the number of clauses of
the input CNF formula."

"`A` unless `B`" is the implication "if not `A` then `B`": if `PK_d` is automatable in polynomial
time on CNF formulas, then CNF-SAT has such an algorithm.

**Formalization Note.** The WPHP Hypothesis is the hypothesis `hW`. Automatability
(`PKAutomatable d`, §2.1.4, p.17) and the CNF-SAT algorithm (`CNFSATSubexp`) share one machine model
(Mathlib's `Turing.FinTM2`) and one input encoding of CNF formulas; both notions are invariant under
polynomial simulations between standard deterministic models. -/
theorem theorem_5_1 (hW : WPHPHypothesis) : ∀ d : ℕ, PKAutomatable d → CNFSATSubexp := by sorry

end Supplement

end RefWPHP
