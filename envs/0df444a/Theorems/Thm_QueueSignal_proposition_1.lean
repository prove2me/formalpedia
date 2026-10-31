-- Prove2me | Theorems.Thm_QueueSignal_proposition_1
-- name    : QueueSignal.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:06:50.571768+00:00
-- url     : https://prove2.me/theorems/e3dea1cd-2bbe-4000-b2dd-33b863d18e13
-- title:
--   Proposition 1 — uninformed customers: the unique pure PSE is $(C,C)$ for $\lambda<\hat\lambda$, $(R,R)$ for $\lambda>\hat\lambda$ (corrected: $\lambda>\hat\lambda$; exception set is a union)
-- statement:
--   Consider a single-server queue whose server is of high quality (reward $V_H$) with prior probability $\delta$ and of low quality (reward $V_L$) otherwise, with exponential service at rate $\mu$, Poisson arrivals at potential rate $\lambda$ and waiting cost $\theta$ per unit time, where $\mu,\theta>0$, $V_H>V_L>\theta/\mu$ and $0<\delta<1$. The server knows its type and chooses to reveal ($R$) or conceal ($C$) its queue; all customers are uninformed of the quality and update their belief from the server's action. Let $\lambda^O(d)$ and $\lambda^U(d)$ be the effective arrival rates (1) and (3) under belief $d$. Then:
--
--   1. the functions $\lambda\mapsto\lambda^O(\delta)$ and $\lambda\mapsto\lambda^U(\delta)$ on $(0,\infty)$ have a unique crossing point $\hat\lambda>0$;
--   2. for every $\lambda>0$ with
--   $$\lambda^O(1)\neq\lambda^U(0)\quad\text{and}\quad\lambda^O(0)\neq\lambda^U(1),$$
--   and every pure signaling profile $\sigma=(s',s'')$:
--      * if $\lambda<\hat\lambda$, then $\sigma$ admits beliefs that make it a pure perfect sequential equilibrium if and only if $\sigma=(C,C)$ (pooling on concealment);
--      * if $\lambda>\hat\lambda$, then $\sigma$ admits beliefs that make it a pure perfect sequential equilibrium if and only if $\sigma=(R,R)$ (pooling on revelation).
--
--   Hence, with only uninformed customers, the queue-disclosure action carries no information about quality: away from finitely many exceptional arrival rates, the pure perfect sequential equilibrium pools, on concealment for small markets and on revelation for large ones.
--
--   **Formalization Note** "The unique pure-strategy perfect sequential equilibrium is $X$" is the equivalence, over the four pure profiles, between "some beliefs make $\sigma$ a pure perfect sequential equilibrium" and "$\sigma=X$". Perfect sequential equilibrium is `QueueSignal.IsPurePSE` (Grossman–Perry: no credible off-path belief makes a deviation strictly profitable).
--
--   Differences from the source:
--   - correction: "otherwise" (λ ≥ λ̂), it is pooling on R → λ > λ̂; reason: at λ = λ̂ both (C,C) and (R,R) (each with off-path belief δ) are pure perfect sequential equilibria, for every admissible parameter tuple; with V_H = 5/2, V_L = 2, µ = 1, θ = 1/2, δ = 1/2 (Example 1, p.554) λ̂ ≈ 0.947 lies outside both exception sets, so the printed statement fails there
--   - correction: "except at those potential arrival rates under which λ^O(1) = λ^U(0) and λ^O(0) = λ^U(1)" (read as a conjunction) → λ is excluded when either equality holds (the union of the two sets); reason: with the parameters above at λ = 1: λ^O(0) = 4/5 = λ^U(1) but λ^O(1) = 5/6 ≠ 3/4 = λ^U(0), and the separating (C,R) with δ^R = 0, δ^C = 1 is a pure perfect sequential equilibrium, though it is neither pooling profile; if "and" lists the two sets, this is the reading of the page
--   - reading: perfect sequential equilibrium via the credible updating rule (Definition 2), with possibly many credible beliefs (footnote 1) → a pure sequential equilibrium such that no credible off-path belief makes some type strictly better off by deviating (Grossman–Perry); reason: the test the paragraph after Definition 2 applies; under the other reading (the equilibrium's own off-path belief must be credible) the proposition is false: with the parameters above at λ = 9/10, (R,R) with δ^C ≈ 0.0951 (both types indifferent) would also qualify
--   - encoding: "the unique crossing point of λ^O(δ) and λ^U(δ)" named λ̂ on p.549 → clause 1 asserts that a positive crossing point exists and is unique, and binds λ̂ to it; reason: the object the page names; it is not a free parameter
--   - encoding: server and customers play the full signaling game; sequential rationality of the customers (Naor's threshold n(δ^R) in the revealed queue, the joining probability p(δ^C) of (2) in the concealed queue) → the server's payoff after R under belief d is λ^O(d) of (1), after C it is λ^U(d) of (3), the same for both types; reason: the paper's own reduction on p.548 (sequential rationality is equivalent to the customers playing (n(δ^R), p(δ^C)) and the server maximizing its effective arrival rate; π_{i,H} = π_{i,L})
--   - encoding: beliefs δ^R, δ^C → real numbers in [0, 1], one per signal (a function Sig → ℝ); reason: Lean convention; same instances
--   - encoding: "the unique pure-strategy perfect sequential equilibrium is pooling on C (resp. R)" → for every pure profile σ: (∃ beliefs making σ a pure perfect sequential equilibrium) ↔ σ = (C,C) (resp. (R,R)); reason: equilibria with the same profile differ only in their off-path beliefs; the paper counts signaling outcomes
-- source:
--   Guo, Haviv, Luo, Wang, Signaling Service Quality Through Queue Disclosure, MSOM 25(2) (2023), doi:10.1287/msom.2022.1170, Proposition 1, p.549

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame
import Definitions.Def_QueueSignal_QueueModel

namespace QueueSignal

/-- **Proposition 1** (Guo, Haviv, Luo, Wang, *Signaling Service Quality Through Queue Disclosure*, MSOM 25(2) (2023),
doi:10.1287/msom.2022.1170, §4.2, p.549, PDF p.8), corrected at `λ = λ̂` and in the
exception set.

Consider the baseline game in which all customers are uninformed of service quality, with
`μ, θ > 0`, `V_H > V_L > θ/μ` and `0 < δ < 1`. Then

1. `λ^O(δ)` and `λ^U(δ)`, as functions of the potential arrival rate `λ > 0`, have a unique
   crossing point `λ̂ > 0`;
2. for every `λ > 0` with `λ^O(1) ≠ λ^U(0)` and `λ^O(0) ≠ λ^U(1)`, and every pure profile `σ`:
   * if `λ < λ̂`, then `σ` (with suitable beliefs) is a pure perfect sequential equilibrium iff
     `σ = (C, C)`;
   * if `λ > λ̂`, then `σ` (with suitable beliefs) is a pure perfect sequential equilibrium iff
     `σ = (R, R)`.

**Formalization Note.** "The unique pure-strategy perfect sequential equilibrium is `X`" is the
iff over the four pure profiles, with the beliefs existentially quantified (equilibria differ
in their off-path beliefs). Perfect sequential equilibrium is `IsPurePSE` (no credible
off-path belief makes a deviation strictly profitable). The printed "otherwise" (`λ ≥ λ̂`) is
corrected to `λ > λ̂`, and the printed exception set "`λ^O(1) = λ^U(0)` and `λ^O(0) = λ^U(1)`" is
read as the union of the two equality sets. -/
theorem proposition_1 (P : Params) (hP : P.Valid) :
    ∃ lhat : ℝ, (0 < lhat ∧ lamO P lhat P.δ = lamU P lhat P.δ) ∧
      (∀ lam : ℝ, 0 < lam → lamO P lam P.δ = lamU P lam P.δ → lam = lhat) ∧
      ∀ lam : ℝ, 0 < lam → lamO P lam 1 ≠ lamU P lam 0 → lamO P lam 0 ≠ lamU P lam 1 →
        ∀ σ : Profile,
          (lam < lhat →
            ((∃ b : Sig → ℝ, IsPurePSE P.δ (pay P lam) σ b) ↔ σ = (.C, .C))) ∧
          (lhat < lam →
            ((∃ b : Sig → ℝ, IsPurePSE P.δ (pay P lam) σ b) ↔ σ = (.R, .R))) := by sorry

end QueueSignal
