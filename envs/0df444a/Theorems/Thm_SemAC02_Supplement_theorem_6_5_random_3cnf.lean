-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_6_5_random_3cnf
-- name    : SemAC02.Supplement.theorem_6_5_random_3cnf
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:51:01.890953+00:00
-- url     : https://prove2.me/theorems/da11df50-56a1-4ab8-b58e-465dbace6b2f
-- title:
--   Theorem 6.5 — random 3-CNFs need semantic ΣΠΣ-PC size 2^{Ω_α(n)}
-- statement:
--   Fix $\alpha>0$ and let $F_{n,\alpha}$ be the random 3-CNF with $m=\lfloor\alpha n\rfloor$ clauses drawn independently and uniformly, with repetition, from the $8\binom n3$ clauses of width exactly three. There is a constant $c=c(\alpha)>0$ such that, with probability $1-o(1)$, every arity-2 semantic ΣΠΣ-PC refutation $\pi$ of $F_{n,\alpha}$ over $\mathbb F_2$ satisfies
--
--   $$
--   S(\pi)\ge 2^{cn},
--   $$
--
--   and consequently its ΣΠΣ-size is at least $2^{cn}$. If $\alpha>\ln2/\ln(8/7)$, then $F_{n,\alpha}$ is also unsatisfiable with probability $1-o(1)$.
--
--   Together with Corollary 6.16 this separates semantic ΣΠΣ-PC from ΣΠΣΠ[3]-PC on random 3-CNFs.
--
--   **Formalization Note** The size bound is a statement for every $\alpha>0$ (vacuous when no refutation exists). The ΣΠΣ-size is `csize`.
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - encoding: size of a proof: distinct rooted subcircuits, sharing across lines → csize: distinct subterms of the lines; reason: a circuit term with equal subterms identified is the DAG with maximal sharing
--   - encoding: with probability 1 − o(1), random formula drawn uniformly with repetition → Tendsto (uniform probability of the event over sequences of clauses) atTop (𝓝 1), constants chosen before n; reason: o(1) failure probability is the statement that the probability tends to 1
--   - encoding: 2^{Ω_α(n)} → ∃ c > 0 depending only on α, bound 2^{cn} inside the event; reason: asymptotic notation as an explicit constant chosen before n
--   - encoding: the formula C₁ ∧ ⋯ ∧ C_m with repetition → seqCNF: the set of the sampled clauses; reason: repeated clauses give the same axioms and the same satisfiability
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 6.5, p.42 (PDF p.44); §6.1, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_clauseAx
import Definitions.Def_SemAC02_Supplement_randCNF

namespace SemAC02.Supplement

open ACirc Filter Topology

/-- **Theorem 6.5 (Random 3-CNFs)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard
Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission), Theorem 6.5, p.42,
for `F_{n,α}` of §6.1, p.41): for every fixed `α > 0`, with probability `1 − o(1)` every semantic
ΣΠΣ-PC refutation `π` of `F_{n,α}` satisfies `S(π) ≥ 2^{Ω_α(n)}`. Consequently, its ΣΠΣ-size is
at least `2^{Ω_α(n)}`. If `α > ln 2/ln(8/7)`, then `F_{n,α}` is also unsatisfiable with
probability `1 − o(1)`.

`F_{n,α}` is a uniformly random sequence of `m = ⌊αn⌋` clauses of width exactly three on
`x₁, …, x_n` (drawn independently, with repetition); its axioms are the clause polynomials over
`𝔽₂`.

**Formalization Note** `2^{Ω_α(n)}` is `2^{cn}` with a constant `c > 0` depending only on `α`,
chosen before `n`; "with probability `1 − o(1)`" says that the probability of the event tends to
`1` as `n → ∞`. The ΣΠΣ-size is the `C`-size `csize`. -/
theorem theorem_6_5_random_3cnf (α : ℝ) (hα : 0 < α) :
    (∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => uprob (fun ω : Fin ⌊α * n⌋₊ → WClause n 3 =>
      ∀ π : List (ACirc (ZMod 2) (Fin n)),
        IsSemPCRef IsSPS Set.univ (clauseAx (seqCNF ω : Set (LiftSAParity.Clause (Fin n)))) π →
        (2 : ℝ) ^ (c * n) ≤ topS Set.univ π ∧ (2 : ℝ) ^ (c * n) ≤ csize π)) atTop (𝓝 1)) ∧
    (Real.log 2 / Real.log (8 / 7) < α →
      Tendsto (fun n : ℕ => uprob (fun ω : Fin ⌊α * n⌋₊ → WClause n 3 =>
        ¬ LiftSAParity.Satisfiable (seqCNF ω))) atTop (𝓝 1)) := by sorry

end SemAC02.Supplement
