-- Prove2me | Theorems.Thm_QAlgorithms_Papers_FGG14b_qaoa1_e3lin2_bound
-- name    : QAlgorithms.Papers.FGG14b.qaoa1_e3lin2_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:45:24.596577+00:00
-- url     : https://prove2.me/theorems/d0b9c3d7-7d35-47c9-b5d8-b79507938dba
-- title:
--   Level-one QAOA on bounded-occurrence Max E3LIN2 satisfies (1/2 + 1/(101 D^{1/2} ln D)) m equations on average
-- statement:
--   This is the main result of Farhi, Goldstone and Gutmann on the level-one Quantum Approximate Optimization Algorithm (QAOA) for bounded-occurrence Max E3LIN2.
--
--   An instance of Max E3LIN2 on $n$ bits is a set of $m$ linear equations over $\mathbb F_2$, each of the form $x_a + x_b + x_c = d \pmod 2$ with three distinct variables $a, b, c$ and right-hand side $d \in \{0,1\}$, at most one equation per triple $\{a,b,c\}$. Let $C(z)$ be the number of equations satisfied by $z \in \{0,1\}^n$, viewed as the diagonal operator $C|z\rangle = C(z)|z\rangle$; let $B = X_1 + \cdots + X_n$ and $|s\rangle = 2^{-n/2}\sum_z |z\rangle$. For real $\gamma, \beta$ put
--
--   $$|\gamma,\beta\rangle = e^{-i\beta B} e^{-i\gamma C} |s\rangle,$$
--
--   so that $F(\gamma,\beta) = \langle \gamma,\beta| C |\gamma,\beta\rangle = \sum_z |\langle z|\gamma,\beta\rangle|^2 C(z)$ is the expected number of equations satisfied by the string obtained by measuring $|\gamma,\beta\rangle$ in the computational basis.
--
--   **Theorem.** There is $D_0$ such that for every integer $D \ge D_0$, every $n$, and every such instance in which each bit occurs in at most $D + 1$ equations, there exists $\gamma$ with $|\gamma| \le \frac{1}{10 D^{1/2}}$ such that
--
--   $$F\Big(\gamma, \frac{\pi}{4}\Big) \;\ge\; \Big(\frac12 + \frac{1}{101\, D^{1/2} \ln D}\Big)\, m.$$
--
--   A uniformly random string satisfies $m/2$ equations on average; the theorem shows that one round of QAOA beats random guessing by a term of order $1/(D^{1/2}\ln D)$, uniformly over all bounded-occurrence instances, and in particular that every such instance has an assignment satisfying that many equations.
--
--   **Formalization Note** The source's qualifier "for large $D$" is rendered as an existential threshold $D_0$ quantified before $D$, $n$ and the instance. The objective is the unshifted count of satisfied equations; the paper's shifted operator (6) differs by the constant $m/2$, which only contributes a global phase to $e^{-i\gamma C}$.
-- source:
--   A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem (Farhi, Goldstone, Gutmann), arXiv:1412.6062v2, §II main result (unnumbered), eqs. (43)–(45), PDF p. 3. https://arxiv.org/abs/1412.6062v2 . PDF SHA-256: b0723913409de0a2c539ddd8fc99591dd541abe8c9c1d8134175259332072c49.

import Definitions.Def_QAlgorithms_Defs_QAOA
set_option autoImplicit false

namespace QAlgorithms.Papers.FGG14b

open QAlgorithms

/-- FGG-E3LIN2 §II, main result (pp.3–4, conclusion (43)–(45), pp.8–9; v2 bound): for large `D`,
for every Max E3LIN2 instance with `m` equations (exactly three distinct variables each, at most
one equation per variable triple, eq. (6)) in which every bit occurs in at most `D + 1` equations
(p.3, p.5), there is `γ ∈ [−1/(10 D^{1/2}), 1/(10 D^{1/2})]` such that, with `β = π/4`, the
expected number of satisfied equations in the measured p = 1 QAOA state `|γ, π/4⟩` is at least
`(1/2 + 1/(101 D^{1/2} ln D)) m`. -/
theorem qaoa1_e3lin2_bound :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ (n : ℕ) (I : E3LIN2Instance n), I.OccurrenceAtMost (D + 1) →
      ∃ γ : ℝ, |γ| ≤ 1 / (10 * Real.sqrt D) ∧
        (1 / 2 + 1 / (101 * Real.sqrt D * Real.log D)) * (I.eqs.card : ℝ) ≤
          qaoaExpectation (fun z => (I.numSatisfied z : ℝ)) 1 (fun _ => Real.pi / 4)
            (fun _ => γ) := by
  sorry

end QAlgorithms.Papers.FGG14b
