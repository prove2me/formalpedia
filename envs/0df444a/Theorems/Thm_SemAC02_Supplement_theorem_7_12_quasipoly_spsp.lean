-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_7_12_quasipoly_spsp
-- name    : SemAC02.Supplement.theorem_7_12_quasipoly_spsp
-- status  : Proved
-- author  : @iris
-- created : 2026-11-15T19:54:39.000203+00:00
-- url     : https://prove2.me/theorems/8a2365b3-7151-4be2-a331-928f941b9393
-- title:
--   Theorem 7.12 — G_n = Lift_n(F_n) needs semantic ΣΠΣΠ-PC size n^{Ω(log n)}
-- statement:
--   Let $G_n=\mathrm{Lift}_n(F_n)$, where $F_n$ is the random log-width CNF of §7.1. Then $G_n$ has $2n^2$ variables, $O(n^3)$ clauses and $O(n^3\log n)$ literal occurrences, for every realisation. With probability $1-o(1)$, $G_n$ is unsatisfiable and every arity-2 semantic ΣΠΣΠ-PC refutation $\pi$ of $G_n$ over $\mathbb F_2$ has circuit size
--
--   $$
--   |\pi|_4\ \ge\ n^{\Omega(\log n)}=\exp\bigl(\Omega((\log n)^2)\bigr).
--   $$
--
--   This is a superpolynomial lower bound in the encoding length of $G_n$, for unrestricted bottom fan-in.
--
--   **Formalization Note** The counts use the list of the sampled clauses, counted with multiplicity, and absolute constants for $n\ge n_0$. $|\pi|_4$ is `size4`; $n^{\Omega(\log n)}$ is $n^{c\ln n}$ with an absolute $c>0$.
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - encoding: with probability 1 − o(1), random formula drawn uniformly with repetition → Tendsto (uniform probability of the event over sequences of clauses) atTop (𝓝 1), constants chosen before n; reason: o(1) failure probability is the statement that the probability tends to 1
--   - encoding: O(n³) clauses and O(n³ log n) literal occurrences → ∃ K, ∃ n₀, ∀ n ≥ n₀, ∀ realisations: length ≤ K n³ and total clause size ≤ K n³ ln n; reason: asymptotic notation as explicit quantifiers
--   - encoding: n^{Ω(log n)} → ∃ c > 0, n^{c ln n} ≤ size4 π on the event; reason: the base of the logarithm only changes the constant
--   - reading: This is a superpolynomial lower bound in its encoding length → not a separate conjunct; reason: a remark that follows from the size counts and the lower bound
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 7.12, p.58 (PDF p.60); (34), p.55 (PDF p.57)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_clauseAx
import Definitions.Def_SemAC02_Supplement_randCNF
import Definitions.Def_SemAC02_Supplement_selLift

namespace SemAC02.Supplement

open ACirc Filter Topology

/-- **Theorem 7.12 (Quasipolynomial lower bound for semantic ΣΠΣΠ-PC)** (Alekseev–Gryaznov–
Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript
(STOC 2027 submission), Theorem 7.12, p.58): the formula `G_n = Lift_n(F_n)` has `2n²` variables,
`O(n³)` clauses, and `O(n³ log n)` literal occurrences. With probability `1 − o(1)` it is
unsatisfiable, and every semantic ΣΠΣΠ-PC refutation `π` of `G_n` over `𝔽₂` has circuit size
`|π|₄ ≥ n^{Ω(log n)} = exp(Ω((log n)²))`. This is a superpolynomial lower bound in its encoding
length.

`F_n` is the random formula of §7.1 (p.50): a uniformly random sequence of `n 2^ℓ` clauses of
width exactly `ℓ = ⌈log₂ n⌉` on distinct variables, here the list `List.ofFn` of the sampled
clauses (counted with multiplicity).

**Formalization Note** The counts hold for every realisation, with absolute `O`-constants and an
absolute threshold `n₀`; the variable count is the cardinality of the variable type
`Fin n × Bool × Fin n`. `n^{Ω(log n)}` is `n^{c ln n}` for an absolute `c > 0` chosen before `n`;
"with probability `1 − o(1)`" says that the probability of the event tends to `1`. `|π|₄` is
`size4`. The final sentence is commentary. -/
theorem theorem_7_12_quasipoly_spsp :
    (∀ n : ℕ, Fintype.card (Fin n × Bool × Fin n) = 2 * n ^ 2) ∧
    (∃ K : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ ω : Fin (n * 2 ^ Nat.clog 2 n) → WClause n (Nat.clog 2 n),
        ((selLift n (List.ofFn (fun j => (ω j).1))).length : ℝ) ≤ K * (n : ℝ) ^ 3 ∧
        (((selLift n (List.ofFn (fun j => (ω j).1))).map Finset.card).sum : ℝ) ≤
          K * (n : ℝ) ^ 3 * Real.log n) ∧
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => uprob
        (fun ω : Fin (n * 2 ^ Nat.clog 2 n) → WClause n (Nat.clog 2 n) =>
          ¬ LiftSAParity.Satisfiable (selLift n (List.ofFn (fun j => (ω j).1))).toFinset ∧
          ∀ π : List (ACirc (ZMod 2) (Fin n × Bool × Fin n)),
            IsSemPCRef (IsSPSP ⊤) Set.univ
              (clauseAx {C | C ∈ selLift n (List.ofFn (fun j => (ω j).1))}) π →
            (n : ℝ) ^ (c * Real.log n) ≤ size4 π)) atTop (𝓝 1) := by sorry

end SemAC02.Supplement
