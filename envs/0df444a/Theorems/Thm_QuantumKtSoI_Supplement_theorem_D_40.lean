-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_D_40
-- name    : QuantumKtSoI.Supplement.theorem_D_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:54:03.927199+00:00
-- url     : https://prove2.me/theorems/799a6fa5-8180-4e23-9a53-1e4c584c3fde
-- title:
--   Theorem D.40, p.187 — Theorem 5.25 for every measure within $B\log+B$ of $\mathrm{qKt}$, in particular for $\mathrm{qKt}_U$
-- statement:
--   Let $\mu$ assign a real number $\mu(y|x)$ to every pair of strings, and suppose that there is a constant $B\ge1$ with
--   $$|\mu(y|x)-\mathrm{qKt}(y|x)|\le B\log(|x|+|y|+2)+B\qquad\text{for all } x,y .$$
--   Then Theorem 5.25 holds with $\mu$ in place of $\mathrm{qKt}$, with an $\eta$ that depends only on $\alpha,\beta,c_A$ and $B$: for all reals $0<\alpha<\beta<1$ and integers $c_A\ge1$ there is $\eta>0$ such that no machine, from some length $n_A$ on, halts on $\langle x,w\rangle$ within $2^{\eta|x|}(|x|+|w|+2)^{c_A}$ steps, accepts with probability at least $2/3$ if $\mu(x|w)\ge\beta|x|$ and rejects with probability at least $2/3$ if $\mu(x|w)\le\alpha|x|$.
--
--   In particular this holds for $\mu=\mathrm{qKt}_U$ for every quasi-linear universal machine $U$, and for every machine $U$ that satisfies Equation (36).
--
--   This extends the exponential hardness of conditional estimation to every measure logarithmically close to $\mathrm{qKt}$.
--
--   **Formalization Note** Quantifier order: for all $\alpha,\beta,c_A,B$ there is $\eta$ that works for every $\mu$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
--   - generalization: Equation (36) refers to the machine I of Theorem D.30 → the Equation (36) clause is stated for every machine I with the Theorem D.30 property; reason: Corollary D.39 uses only that property of I; the paper's I has it
--   - encoding: qKt_U, with the minimum of the empty set equal to +∞ → qKt_U is ℕ∞-valued; the statement first asserts that it is finite everywhere and then reads its values as reals; reason: the restated results are inequalities between finite values; finiteness holds for every polynomially universal machine (p.118)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem D.40, p.187; Theorem 5.25, p.75; Equation (36), p.186

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_qKtU
import Definitions.Def_QuantumKtSoI_Supplement_Thm525For

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem D.40** (Hardness of estimating a comparable measure; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.187). Let `µ` assign a real
number `µ(y|x)` to every pair of strings, write `µ(y) = µ(y|ε)`, and suppose that there is a constant
`B ≥ 1` with `|µ(y|x) − qKt(y|x)| ≤ B log(|x|+|y|+2) + B` for all strings `x, y`. Then Theorem 5.25
holds with `µ` in place of `qKt`, with an `η` that depends on `α, β, c_A` and `B`. In particular, it
holds for `µ = qKt_U` for every quasi-linear universal machine `U`, and for every machine `U` that
satisfies Equation (36).

**Formalization Note** Quantifier order: `∀ α β c_A B, ∃ η, ∀ µ` (`η` does not depend on `µ`).
`NoSep µ α β c_A η` is the conclusion of Theorem 5.25 for `µ` at that `η`, and `Thm525For µ` is
Theorem 5.25 for `µ` (module `Thm525For`). The `qKt_U` clauses first assert that `qKt_U`
(`ℕ∞`-valued, p.117) is finite, then read its values in `ℝ`. Equation (36) refers to "the machine
`I` of Theorem D.30"; that clause is stated for every machine `I` with the Theorem D.30 property
(`InterpreterProp`), as in Theorem D.34: the proof (Corollary D.39, through Lemma D.33) uses only
that property of `I`, and the paper's `I` has it.
`G` is any admissible glue routine set (p.24). -/
theorem theorem_D_40 (G : GlueRoutines) (hG : G.Admissible) :
    (∀ α β : ℝ, 0 < α → α < β → β < 1 → ∀ cA : ℕ, 1 ≤ cA → ∀ B : ℝ, 1 ≤ B →
      ∃ η : ℝ, 0 < η ∧ ∀ μ : List Bool → List Bool → ℝ,
        (∀ x y : List Bool,
          |μ y x - qKt G y x| ≤ B * Real.logb 2 ((x.length : ℝ) + y.length + 2) + B) →
        NoSep μ α β cA η) ∧
    (∀ U : CodedMachine, QuasiLinUniversal U →
      (∀ y x : List Bool, qKtU U y x ≠ ⊤) ∧ Thm525For fun y x => ((qKtU U y x).toNat : ℝ)) ∧
    ∀ I : CodedMachine, ∀ pI : Polynomial ℝ, InterpreterProp G I pI →
      ∀ U : CodedMachine, Eq36 I U →
        (∀ y x : List Bool, qKtU U y x ≠ ⊤) ∧ Thm525For fun y x => ((qKtU U y x).toNat : ℝ) := by sorry

end QuantumKtSoI.Supplement
