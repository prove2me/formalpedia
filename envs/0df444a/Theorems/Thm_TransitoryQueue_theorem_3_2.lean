-- Prove2me | Theorems.Thm_TransitoryQueue_theorem_3_2
-- name    : TransitoryQueue.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:01:26.330004+00:00
-- url     : https://prove2.me/theorems/bb4bfa5d-0be1-4284-a2e8-665603c66d56
-- title:
--   Theorem 3.2 with Remark 8.3 — KMT strong embedding of the uniform empirical process, one bridge
-- statement:
--   There are constants $C,K,\lambda>0$ and a probability space carrying one Brownian bridge $Y$ and, for each $n\ge1$, independent $U[0,1]$ random variables $U_{n,1},\dots,U_{n,n}$ such that, with the uniform empirical process
--
--   $$\alpha_n(s)=\sqrt n\bigl(F_n(s)-s\bigr),\qquad F_n(s)=\frac1n\sum_{i=1}^{n}\mathbf 1\{U_{n,i}\le s\},$$
--
--   for all $n\ge1$ and $x\in\mathbb R$:
--
--   $$P\Bigl(\sup_{s\in[0,1]}\sqrt n\,\bigl|\alpha_n(s)-Y(s)\bigr|>C\log n+x\Bigr)<Ke^{-\lambda x}.$$
--
--   This is the KMT theorem for the empirical process in the form of Remark 8.3 ("There exists a Brownian bridge $B$ such that for each $n$, there exists $n$ independent uniforms $U_1,\dots,U_n$ whose empirical process $\alpha_n$ satisfies …"), which is the form in which one bridge serves all $n$.
--
--   **Formalization Note** The law $U[0,1]$ is Lebesgue measure restricted to $[0,1]$. Remark 3.3's values $C=100$, $K=10$, $\lambda=1/50$ are not asserted.
--
--   Differences from the source:
--   - reading: Theorem 3.2: one sequence U_1, U_2, … and a sequence of bridges B^br_1, B^br_2, … → Remark 8.3: one bridge Y and, for each n, uniforms U_{n,1}, …, U_{n,n}; reason: Remark 8.3 is the paper's own restatement of (16) with one bridge, and this is the form the mission's coupling uses; the constants are those of (16)
--   - encoding: P(sup_{s∈[0,1]} … > a) → P of the event that some s ∈ [0, 1] exceeds a; reason: the same event
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Theorem 3.2, eq. (16), p.10; Remark 8.3, p.46

import Mathlib
import Definitions.Def_TransitoryQueue_IsBrownianBridge
open MeasureTheory ProbabilityTheory

namespace TransitoryQueue

/-- **Theorem 3.2 (KMT strong embedding of the uniform empirical process), in the form of
Remark 8.3.** There are constants `C, K, λ > 0` and a probability space carrying one Brownian
bridge `Y` and, for each `n ≥ 1`, `n` independent `U[0,1]` variables `U_1, …, U_n` whose empirical
process `α_n(s) = √n (F_n(s) - s)`, `F_n(s) = n^{-1} Σ_i 1{U_i ≤ s}`, satisfies for all `x ∈ ℝ`
`P(sup_{s ∈ [0,1]} √n |α_n(s) - Y(s)| > C log n + x) < K e^{-λ x}`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Theorem 3.2, p.10, eq. (16), and Remark 8.3, p.46 ("There exists a Brownian bridge B such
that for each n, there exists n independent uniforms U_1, …, U_n …").

**Formalization Note** One bridge for all `n` with uniforms depending on `n` (Remark 8.3). Theorem
3.2's sequence of bridges `B^{br}_n` is the special case `B^{br}_n = Y`. Remark 3.3's values
`C = 100`, `K = 10`, `λ = 1/50` are not asserted. "sup > a" is written "some `s` has value > a". -/
theorem theorem_3_2 :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (Y : ℝ → Ω → ℝ) (U : (n : ℕ) → Fin n → Ω → ℝ),
        IsBrownianBridge Y P ∧ (∀ n, iIndepFun (U n) P) ∧
        (∀ n i, HasLaw (U n i) (volume.restrict (Set.Icc (0 : ℝ) 1)) P) ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
          P.real {ω | ∃ s ∈ Set.Icc (0 : ℝ) 1, C * Real.log n + x <
              Real.sqrt n * |Real.sqrt n *
                (((Finset.univ.filter (fun i : Fin n => U n i ω ≤ s)).card : ℝ) / n - s) - Y s ω|}
            < K * Real.exp (-(lam * x)) := by sorry

end TransitoryQueue
