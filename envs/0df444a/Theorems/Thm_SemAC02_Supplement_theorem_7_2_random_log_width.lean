-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_7_2_random_log_width
-- name    : SemAC02.Supplement.theorem_7_2_random_log_width
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:52:50.810731+00:00
-- url     : https://prove2.me/theorems/3a4ee248-069e-4cab-8ddf-6f4d7984d5d5
-- title:
--   Theorem 7.2 — random log-width CNFs need semantic ΣΠΣΠ[w]-PC size (1/4)exp(an/(wC^w))
-- statement:
--   Let $F_n$ be the random CNF with $m=n2^\ell$ clauses, $\ell=\lceil\log_2n\rceil$, drawn independently and uniformly, with repetition, from the clauses of width exactly $\ell$ on distinct variables. There are absolute constants $a>0$, $C>1$ and $c>0$ such that, with probability $1-o(1)$, $F_n$ is unsatisfiable and, simultaneously for every integer $1\le w\le c\log_2n$, every arity-2 semantic ΣΠΣΠ[$w$]-PC refutation $\pi$ over $\mathbb F_2$ satisfies
--
--   $$
--   S(\pi)\ \ge\ \frac14\exp\Bigl(\frac{an}{wC^w}\Bigr). \tag{27}
--   $$
--
--   The same bound holds for total circuit size; the constants are independent of $n$ and $w$.
--
--   These formulas are the base of the lifted formulas $G_n$ of Theorem 7.12.
--
--   **Formalization Note** One event covers all $w$ in the range. Total circuit size is `csize`.
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - generalization: the same lower bound for total circuit size (|π|₄ = Σ_v |C_v|, (32), p.55) → the bound for csize, the number of distinct subterms across all lines; reason: csize ≤ |π|₄, so the csize bound implies the |π|₄ bound; if total circuit size is read as the C-size of p.15 it is that measure
--   - encoding: with probability 1 − o(1), random formula drawn uniformly with repetition → Tendsto (uniform probability of the event over sequences of clauses) atTop (𝓝 1), constants chosen before n; reason: o(1) failure probability is the statement that the probability tends to 1
--   - encoding: ℓ = ⌈log₂ n⌉ → Nat.clog 2 n; reason: Mathlib's ceiling logarithm
--   - encoding: F_n = the m sampled clauses, with repetition → seqCNF: the set of the sampled clauses; reason: repeated clauses give the same axioms and the same satisfiability
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 7.2, p.51 (PDF p.53); §7.1, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_clauseAx
import Definitions.Def_SemAC02_Supplement_randCNF

namespace SemAC02.Supplement

open ACirc Filter Topology

/-- **Theorem 7.2 (Random logarithmic-width CNFs)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–
Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission),
Theorem 7.2, p.51, for `F_n` of §7.1, p.50): there are absolute constants `a > 0`, `C > 1`, and
`c > 0` such that, with probability `1 − o(1)`, `F_n` is unsatisfiable and simultaneously for every
integer `1 ≤ w ≤ c log₂ n`, every semantic ΣΠΣΠ[w]-PC refutation `π` over `𝔽₂` satisfies
`S(π) ≥ (1/4) exp(an/(wC^w))` (27). The same lower bound holds for total circuit size. The
constants are independent of both `n` and `w`.

`F_n` is a uniformly random sequence of `m = n 2^ℓ` clauses of width exactly `ℓ = ⌈log₂ n⌉` on
distinct variables among `x₁, …, x_n` (drawn independently, with repetition).

**Formalization Note** `⌈log₂ n⌉` is `Nat.clog 2 n`. "With probability `1 − o(1)`": the probability
of the single event "unsatisfiable, and the bound holds for every `w` in the range" tends to `1`;
`a`, `C`, `c` are chosen before `n`. Total circuit size is the `C`-size `csize`. -/
theorem theorem_7_2_random_log_width :
    ∃ a C c : ℝ, 0 < a ∧ 1 < C ∧ 0 < c ∧
      Tendsto (fun n : ℕ => uprob
        (fun ω : Fin (n * 2 ^ Nat.clog 2 n) → WClause n (Nat.clog 2 n) =>
          ¬ LiftSAParity.Satisfiable (seqCNF ω) ∧
          ∀ w : ℕ, 1 ≤ w → (w : ℝ) ≤ c * Real.logb 2 n →
            ∀ π : List (ACirc (ZMod 2) (Fin n)),
              IsSemPCRef (IsSPSP (w : ℕ∞)) Set.univ
                (clauseAx (seqCNF ω : Set (LiftSAParity.Clause (Fin n)))) π →
              1 / 4 * Real.exp (a * n / (w * C ^ w)) ≤ topS Set.univ π ∧
              1 / 4 * Real.exp (a * n / (w * C ^ w)) ≤ csize π)) atTop (𝓝 1) := by sorry

end SemAC02.Supplement
