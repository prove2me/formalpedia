-- Prove2me | Theorems.Thm_SATotalCoeffLB_theorem_3
-- name    : SATotalCoeffLB.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:39.969107+00:00
-- url     : https://prove2.me/theorems/69f1288d-1abe-48b3-af98-6f176db87530
-- title:
--   Theorem 3 — Sherali–Adams refutations of AND and parity checks need $\sum_{i<j}\|C_{ij}\|_1\ge 2^{an}$
-- statement:
--   There are constants $a, c > 0$ and $J \in \mathbb N$ such that, for infinitely many $n$, there are $t = O(n)$ additional variables $T_1, \dots, T_t$ and $O(n)$ parity checks $q_e = (1 - s_e Y_e \prod_{j\in S_e} T_j)/2$ for $e \in E \subseteq \binom{[n]}{2}$, with fixed signs $s_e \in \{\pm1\}$ and sets $S_e \subseteq [t]$ of size $|S_e| \le J - 1$, for which the following hold.
--
--   1. The system $\mathcal P = \{p_{ij} : i < j\} \cup \{q_e : e \in E\}$, where $p_{ij} = (1 - Y_{ij}\omega_{ij}(X))/2$ are the AND gate checks for **all** pairs $i<j$, is unsatisfiable. Every equation is a $J$-junta with coefficients of magnitude at most $1/2$.
--   2. For every integer $1 \le k \le cn$, every identity
--   $$
--   -1 = \sum_j h_j^2 + \sum_{i<j} C_{ij}\, p_{ij} + \sum_{e\in E} D_e\, q_e
--   $$
--   in the Boolean quotient ring $\mathbb R[X, Y, T]/\langle y^2-1 : y \in X\cup Y\cup T\rangle$, in which each $h_j$ depends on at most $k$ variables and all multipliers have arbitrary degree, satisfies
--   $$
--   \sum_{i<j} \|C_{ij}\|_1 \ge 2^{an},
--   $$
--   where $\|f\|_1$ is the sum of the absolute values of the coefficients of the multilinear polynomial $f$.
--
--   This is the first exponential lower bound on the total coefficient size of Sherali–Adams refutations in the $\{\pm1\}$ basis for an explicit system of constant-size constraints. Only the multipliers $C_{ij}$ of the AND checks are charged, which makes the bound stronger than one on a total size that also charges the squares and the $D_e$. Corollary 1 of the paper derives from it a refutation of the low-norm Nullstellensatz hypothesis for the AND code of Devadas–Hopkins–Kalai–Kothari–Lombardi–Mathialagan.
--
--   **Formalization Note** The constant hidden in $t = O(n)$ and $O(n)$ parity checks is a single constant $K$ chosen together with $a$, $c$, $J$, before $n$.
--
--   Differences from the source:
--   - reading: $t = O(n)$ additional variables and $O(n)$ parity checks → one constant $K$, quantified with $a, c, J$ before $n$, with $t \le Kn$ and $|E| \le Kn$; reason: the sentence fixes its constants before 'for infinitely many $n$'; an $n$-dependent constant would make the clause empty; the proof gives $|E| = m \le 4n$ and $t \le Bm$
--   - encoding: for infinitely many $n$ → for every $N$ there is $n \ge N$; reason: equivalent for subsets of $\mathbb N$
--   - encoding: the Boolean quotient ring $\mathbb R[\text{variables}]/\langle y^2-1\rangle$ → real functions on bit vectors, variable $v$ evaluating to $(-1)^{x_v}$ (`CubeFn`); reason: for finitely many variables evaluation on the $\pm1$ cube is a ring isomorphism; same identities
--   - encoding: $\|f\|_1$; coefficients of an equation; $J$-junta, '$h_j$ depends on at most $k$ variables' → `coeffNorm` (sum of $|\widehat f(U)|$ over all $U$); `coeff` $\widehat f(U)$ for every monomial $U$; `DependsOnAtMost`, counting $X$, $Y$, $T$ variables alike; reason: the multilinear representative is unique; same quantities
--   - encoding: signs $s_e \in \{\pm1\}$ and sets $S_e$ for $e \in E$; a finite family $(h_j)_j$; multipliers $C_{ij}$, $D_e$ → functions $\sigma$, $S$ on all pairs, constrained and used only for $e \in E$, with $\sigma_e = 1 \lor \sigma_e = -1$; $h$ indexed by $\{0,\dots,r-1\}$; $C$, $D$ functions on all pairs, $D_e$ used only for $e \in E$; reason: values off $E$ never enter the statement
--   - encoding: $|S_e| \le J - 1$ → natural-number subtraction $J - 1$; reason: differs only at $J = 0$, which item 1 already excludes since $p_{ij}$ depends on three variables
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Theorem 3, p.9 (restated with H, Section 9, p.49)

import Mathlib
import Definitions.Def_SATotalCoeffLB_andCheck
import Definitions.Def_SATotalCoeffLB_parityCheck
import Definitions.Def_SATotalCoeffLB_coeff
import Definitions.Def_SATotalCoeffLB_coeffNorm
import Definitions.Def_SATotalCoeffLB_DependsOnAtMost

namespace SATotalCoeffLB

/-- **Theorem 3 (exponential total coefficient size lower bound for Sherali–Adams)**, p.9
(restated p.49) of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

There are constants `a, c > 0` and `J ∈ ℕ` (and a constant `K` for the `O(n)` bounds) such that for
infinitely many `n` there are `t ≤ Kn` additional variables `T_1, …, T_t` and parity checks `q_e`,
`e ∈ E ⊆ ([n] choose 2)`, `|E| ≤ Kn`, with signs `s_e ∈ {±1}` and sets `S_e ⊆ [t]` of size
`|S_e| ≤ J − 1`, such that
1. the system `P = {p_ij : i < j} ∪ {q_e : e ∈ E}` is unsatisfiable, and every equation is a
   `J`-junta with coefficients of magnitude at most `1/2`;
2. for every integer `1 ≤ k ≤ cn`, every identity
   `−1 = ∑_j h_j² + ∑_{i<j} C_ij p_ij + ∑_{e∈E} D_e q_e` in `ℝ[X, Y, T]/⟨y² − 1⟩`, in which each `h_j`
   depends on at most `k` variables and the multipliers are arbitrary, satisfies
   `∑_{i<j} ‖C_ij‖₁ ≥ 2^{an}`.

**Formalization Note** The Boolean quotient ring is the ring of real functions on the cube
(`CubeFn`), `‖·‖₁` is `coeffNorm` (sum of the absolute values of the multilinear coefficients),
"for infinitely many `n`" is `∀ N, ∃ n ≥ N`, and `t = O(n)`, `|E| = O(n)` use one constant `K`
fixed with `a, c, J`. Signs are reals `±1`; `S_e`, `s_e` are given on all pairs and used for
`e ∈ E` only; the family `(h_j)` is indexed by `Fin r`. -/
theorem theorem_3 :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∃ J K : ℕ, ∀ N : ℕ, ∃ n ≥ N, ∃ t : ℕ, t ≤ K * n ∧
      ∃ (E : Finset (Pair n)) (S : Pair n → Finset (Fin t)) (σ : Pair n → ℝ),
        E.card ≤ K * n ∧ (∀ e ∈ E, (S e).card ≤ J - 1) ∧ (∀ e ∈ E, σ e = 1 ∨ σ e = -1) ∧
        -- item 1
        (¬ ∃ x : Var n t → ZMod 2,
          (∀ e : Pair n, andCheck t e x = 0) ∧ ∀ e ∈ E, parityCheck (S e) (σ e) e x = 0) ∧
        (∀ e : Pair n, DependsOnAtMost J (andCheck t e) ∧
          ∀ U : Finset (Var n t), |coeff (andCheck t e) U| ≤ 1 / 2) ∧
        (∀ e ∈ E, DependsOnAtMost J (parityCheck (S e) (σ e) e) ∧
          ∀ U : Finset (Var n t), |coeff (parityCheck (S e) (σ e) e) U| ≤ 1 / 2) ∧
        -- item 2
        ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ c * n →
          ∀ (r : ℕ) (h : Fin r → CubeFn (Var n t)) (C D : Pair n → CubeFn (Var n t)),
            (∀ j, DependsOnAtMost k (h j)) →
            (-1 : CubeFn (Var n t)) = ∑ j, h j ^ 2 + ∑ e, C e * andCheck t e +
              ∑ e ∈ E, D e * parityCheck (S e) (σ e) e →
            (2 : ℝ) ^ (a * n) ≤ ∑ e, coeffNorm (C e) := by sorry

end SATotalCoeffLB
