-- Prove2me | Theorems.Thm_StochasticProg_Recourse_thm8_attainment
-- name    : StochasticProg.Recourse.thm8_attainment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-18T04:48:07.030919+00:00
-- url     : https://prove2.me/theorems/d74bda2c-b7dd-457c-8135-17eaff83cd2e
-- title:
--   Chapter 3, Theorem 8 -- attainment of the optimal value
-- statement:
--   **Chapter 3, Theorem 8.** Suppose the deterministic-equivalent objective $z(x) = c^{\mathsf
--   T}x+Q(x)$ has a finite infimum over $K = K_1 \cap K_2$, and suppose either
--
--   (a) $K$ is bounded; or
--
--   (b) $Q$ is *eventually linear* along every recession direction $v$ of $K$: for every $x \in K$
--   and every $v$ with $x + \lambda v \in K$ for all $\lambda \ge 0$, there is $\bar\lambda \ge
--   0$ (depending on $x$) and a constant $\mathrm{rc}Q(v)$ such that $Q(x+\lambda v) = Q(x +
--   \bar\lambda v) + (\lambda - \bar\lambda)\,\mathrm{rc}Q(v)$ for all $\lambda \ge
--   \bar\lambda$.
--
--   Then the infimum is attained: some $x^* \in K$ achieves $z(x^*) = \inf_{x \in K} z(x)$.
--
--   The theorem answers the question the book raises before stating it: a finite infimum need not be
--   attained (its Example (1.11), an exponential-tail bid problem, has infimum $0$ attained by no
--   finite $x$); conditions (a)/(b) rule this out.
--
--   **Formalization Note.** Condition (b) is stated with exactly the book's own quantifier order: the
--   threshold $\bar\lambda$ and the recession value $\mathrm{rc}Q(v)$ are existentially introduced
--   per $(x, v)$-pair for $\mathrm{rc}Q$'s dependence on $v$ only, matching Eq. in Theorem 8(b)
--   verbatim rather than a stronger uniform version.
--
--   **Moderator's note.** The book's standing assumption for §3.1c–e (p. 112: "assuming it is not −∞") is stated explicitly: no second-stage problem is unbounded below (`Q(x, ξ_k) ≠ −∞` for every `x` and scenario `k`; for the abstract `Q` of Corollary 10, `Q x ≠ −∞`). Without it "finite on K₂" and the KKT characterisation can fail.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 115-116, Chapter 3, Theorem 8

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance

namespace StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 3, Theorem 8 (p. 115): if the deterministic-equivalent problem has a
finite optimal value and either (a) the feasible region `K1 ∩ K2` is bounded, or
(b) `Q` is eventually linear along every recession direction of `K1 ∩ K2` with a
constant recession value `rcQ v` (the book's own condition, stated with its own
quantifier structure: the threshold `λ̄` may depend on `x`), then the optimal value
is attained by some `x ∈ K1 ∩ K2`. -/
theorem thm8_attainment (inst : Instance n1 n2 m1 m2 K)
    (hQ : ∀ x k, QVal inst x k ≠ ⊥)
    (hfin : ∃ z0 : ℝ, sInf (obj inst '' (K1 inst ∩ K2 inst)) = (z0 : EReal))
    (hcond :
      Bornology.IsBounded (K1 inst ∩ K2 inst) ∨
        ∃ rcQ : (Fin n1 → ℝ) → ℝ,
          ∀ x ∈ K1 inst ∩ K2 inst, ∀ v : Fin n1 → ℝ,
            (∀ lam : ℝ, 0 ≤ lam → x + lam • v ∈ K1 inst ∩ K2 inst) →
            ∃ lam0 : ℝ, 0 ≤ lam0 ∧
              ∀ lam : ℝ, lam0 ≤ lam →
                Q inst (x + lam • v) =
                  Q inst (x + lam0 • v) + (((lam - lam0) * rcQ v : ℝ) : EReal)) :
    ∃ x ∈ K1 inst ∩ K2 inst, obj inst x = sInf (obj inst '' (K1 inst ∩ K2 inst)) := by sorry

end StochasticProg.Recourse
