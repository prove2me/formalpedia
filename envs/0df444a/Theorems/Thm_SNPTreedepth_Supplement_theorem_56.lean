-- Prove2me | Theorems.Thm_SNPTreedepth_Supplement_theorem_56
-- name    : SNPTreedepth.Supplement.theorem_56
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:57:48.345207+00:00
-- url     : https://prove2.me/theorems/eb02238d-e3c8-4a3c-be5e-781d422010bd
-- title:
--   Theorem 56 — a fixed MaxSNP$_0$ problem that is NP-complete on structures of treedepth $\le 2$
-- statement:
--   There is a fixed quantifier-free formula $\psi(A,x_1,\dots,x_{10})$, where $A$ is a binary relation variable, for which the following decision problem is NP-complete: given a relational structure $R$ and an integer $p$, decide whether there is a relation $A\subseteq V(R)^2$ such that
--   $$
--   \bigl|\{\bar v\in V(R)^{10} : R\models\psi(A,\bar v)\}\bigr|\ \ge\ p .
--   $$
--   This holds even when $\mathrm{td}(R)\le2$.
--
--   The statement has both clauses for the same $\psi$: the problem on all input structures is NP-complete, and so is its restriction to $\mathrm{td}(R)\le2$. Here the signature of the input relations of $R$ is fixed together with $\psi$, the count ranges over all $10$-tuples (repetitions allowed), and $p$ is written in binary. The theorem shows that the treedepth metatheorem for SNP does not extend to the optimization class MaxSNP$_0$ unless P = NP.
--
--   **Formalization Note** $\psi$ is the matrix of a base SNP sentence with one relation variable of arity $2$ and $10$ element variables; NP-completeness is Cook's, over the binary alphabet, with the code of `instanceCode`.
--
--   Differences from the source:
--   - encoding: quantifier-free formula ψ(A, x₁, …, x₁₀) → a negation-normal-form matrix NNF (Atom σ 1 (fun _ => 2) 10) of the base sentence syntax, over a signature σ chosen together with ψ; reason: every quantifier-free formula is equivalent to one in negation normal form; the problem's input signature is fixed by the problem
--   - encoding: given a relational structure R and an integer p … NP-complete … This holds even when td(R) ≤ 2 → CookPvsNP.NPComplete of the language {structureIntCode R p | R on Fin n, ∃ A ⊆ (Fin n)², p ≤ #{v̄ : R ⊨ ψ(A, v̄)}} over Bool, and CookPvsNP.NPComplete of the same language with td R ≤ 2 added; reason: Cook's classes are classes of languages over a finite alphabet; structures on Fin n represent every finite structure up to isomorphism; the restriction to treedepth ≤ 2 is part of the language
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Theorem 56, p.53 (PDF p.54); MaxSNP₀, §6.3, p.53

import Mathlib
import Definitions.Def_SNPTreedepth_Structure
import Definitions.Def_SNPTreedepth_Sentence
import Definitions.Def_SNPTreedepth_treedepth
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SNPTreedepth_Supplement_instanceCode

set_option autoImplicit false

namespace SNPTreedepth.Supplement

open SNPTreedepth

/-- **Theorem 56** (Depian, Ganian, Greilhuber, Gründel, Wietheger, *A Uniform Algorithm for Strict NP on
Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…), p.53 (PDF p.54)):
"There is a fixed quantifier-free formula ψ(A, x₁, …, x₁₀), where A is a binary relation variable,
for which the following decision problem is NP-complete: Given a relational structure R and an
integer p, determine whether there is a relation A ⊆ V(R)² such that
|{v̄ ∈ V(R)¹⁰ | R ⊨ ψ(A, v̄)}| ≥ p. This holds even when td(R) ≤ 2."

**Formalization Note** The signature `σ` of the input relations and the quantifier-free formula `ψ`
are fixed before both languages. `ψ` is the matrix (in negation normal form, which every
quantifier-free formula has an equivalent of) of the base `Sentence σ` with one relation variable
of arity `2` and `10` element variables; `R ⊨ ψ(A, v̄)` is the base `Sentence.Holds R (fun _ => A) v̄`.
The statement has the paper's two clauses for the same `σ, ψ`: the decision problem on all input
structures is NP-complete (the language of the binary codes `structureIntCode R p`, structure on
`Fin n`, any `n`, integer `p` in binary, for which some `A ⊆ V(R)²` satisfies the count bound), and
"this holds even when td(R) ≤ 2" (the same language with `td(R) ≤ 2` added). The count is over all
`10`-tuples, repetitions allowed. NP-completeness is Cook's (`CookPvsNP.NPComplete`). -/
theorem theorem_56 :
    ∃ (σ : Signature) (ψ : NNF (Atom σ 1 (fun _ => 2) 10)),
      CookPvsNP.NPComplete
        {w : List Bool | ∃ (n : ℕ) (R : Structure σ (Fin n)) (p : ℤ),
          w = structureIntCode R p ∧
          ∃ A : Set (Fin 2 → Fin n),
            p ≤ ((Set.ncard {v : Fin 10 → Fin n |
              (⟨1, fun _ => 2, 10, ψ⟩ : Sentence σ).Holds R (fun _ => A) v} : ℕ) : ℤ)} ∧
      CookPvsNP.NPComplete
        {w : List Bool | ∃ (n : ℕ) (R : Structure σ (Fin n)) (p : ℤ),
          w = structureIntCode R p ∧ td R ≤ 2 ∧
          ∃ A : Set (Fin 2 → Fin n),
            p ≤ ((Set.ncard {v : Fin 10 → Fin n |
              (⟨1, fun _ => 2, 10, ψ⟩ : Sentence σ).Holds R (fun _ => A) v} : ℕ) : ℤ)} := by sorry

end SNPTreedepth.Supplement
