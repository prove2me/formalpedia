-- Prove2me | Theorems.Thm_RobustObedientPersuasion_Saddle_theorem_3_1
-- name    : RobustObedientPersuasion.Saddle.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:16.787196+00:00
-- url     : https://prove2.me/theorems/de817ce0-0aeb-4695-8d88-94846479583f
-- title:
--   Theorem 3.1 — robust persuasion has a pure-strategy saddle point, max-min = min-max, and vertex worst-case priors
-- statement:
--   Let $\Omega$ and $A$ be finite, $u,v:\Omega\times A\to\mathbb R$ the Receiver's and Sender's utilities, and $\alpha\in\Delta(A)$ satisfy the conditions of Lemma 2.1 (no action in $\operatorname{supp}(\alpha)$ is statewise strictly dominated, i.e. $M_a\ne\emptyset$ for each supported $a$). Let $\mathcal P(\alpha)$ be the identified set of priors, $\Pi_{RO}(\alpha)$ the robustly obedient direct policies and $V(\pi\mid\mu)$ the Sender's payoff, and suppose $\Pi_{RO}(\alpha)\neq\emptyset$. Then:
--
--   1. All the extrema below are attained, and
--   $$\max_{\pi\in\Pi_{RO}(\alpha)}\ \min_{\mu\in\mathcal P(\alpha)}V(\pi\mid\mu)=\min_{\mu\in\mathcal P(\alpha)}\ \max_{\pi\in\Pi_{RO}(\alpha)}V(\pi\mid\mu).$$
--   2. There exist $\pi^s\in\Pi_{RO}(\alpha)$ and $\mu^s\in\mathcal P(\alpha)$ such that
--   $$V(\pi\mid\mu^s)\le V(\pi^s\mid\mu^s)\le V(\pi^s\mid\mu)\qquad\forall\pi\in\Pi_{RO}(\alpha),\ \forall\mu\in\mathcal P(\alpha).$$
--   3. For every fixed $\pi\in\Pi_{RO}(\alpha)$ the inner minimization $\min_{\mu\in\mathcal P(\alpha)}V(\pi\mid\mu)$ is attained at an extreme point of $\mathcal P(\alpha)$.
--   4. In particular, every maxmin-optimal policy $\pi^s$ admits a worst-case prior $\widehat\mu\in\operatorname{ext}(\mathcal P(\alpha))$.
--
--   This is the paper's main structural result: once recommendations are required to be obedient uniformly over the data-identified priors, the Sender's robust persuasion problem becomes a bilinear game with a pure-strategy saddle point, and the worst case for any fixed policy can be found among the finitely many vertices of the identified polytope. The saddle prior $\mu^s$ itself need not be a vertex.
--
--   **Formalization Note** "max" and "min" are encoded with `IsGreatest`/`IsLeast` on the image sets, so every inner and outer extremum is asserted to exist rather than defaulted: the first two conjuncts give the inner minimum for every policy and the inner maximum for every prior; the third gives a common value $w$ that is the greatest inner-minimum value and the least inner-maximum value. A maxmin-optimal policy is one whose inner minimum equals that greatest inner-minimum value.
--
--   Differences from the source:
--   - reading: "no action in supp(α) is statewise strictly dominated under u" → every M_a with α(a) > 0 is nonempty; reason: the paper states (p. 3) that this condition is equivalent to the existence of a posterior under which each supported action is optimal, and Appendix A uses exactly that meaning; this is domination by mixed actions (by the separating-hyperplane lemma, a is undominated by every mixed action iff M_a is nonempty), whereas the pure-action reading would make the lemma false (u(a,·) = (0.4, 0.4), u(a₁,·) = (1, 0), u(a₂,·) = (0, 1) — a is not dominated by a pure action yet M_a = ∅, so P(α) = ∅ when α(a) > 0)
--   - generalization: the model assumes a true prior μ₀ ∈ int Δ(Ω) rationalizing α → no μ₀ appears; reason: μ₀ does not enter P(α), Π_RO(α), V or the conclusion, so the Lean statement covers every α of the source and specializes to it
--   - encoding: max/min notation (attainment implicit) → IsGreatest/IsLeast on image sets with attainment of every inner and outer extremum stated as conjuncts; reason: real sup/inf would default on ill-posed inputs; this states exactly the source's attained extrema
--   - encoding: u(a, ω), v(a, ω), π(a | ω) → state-first arrays u ω a, v ω a, π ω a; reason: Lean indexing convention, same instances
-- source:
--   Shabab Neel, Robustly Obedient Data Driven Persuasion under State-dependent Sender Payoffs, STOC 2027 submission #51 (October 2026), PDF SHA-256 c8d16d8d566dd78eea1f7db42ce72f49000256f933311c4daac2de1df952b40d, Theorem 3.1, PDF p. 4; proof in Appendix D, PDF pp. 8–9

import Mathlib
import Definitions.Def_RobustObedientPersuasion_Saddle_Model

namespace RobustObedientPersuasion.Saddle

theorem theorem_3_1 {Ω A : Type*} [Fintype Ω] [Fintype A]
    (u v : Ω → A → ℝ) (α : A → ℝ) (hα : α ∈ stdSimplex ℝ A)
    (hdom : NoSupportedActionDominated u α)
    (hRO : (robustlyObedientPolicies u α).Nonempty) :
    -- for every policy, the inner minimum over priors is attained
    (∀ π ∈ robustlyObedientPolicies u α,
      ∃ m, IsLeast ((fun μ => senderPayoff v α π μ) '' identifiedSet u α) m) ∧
    -- for every prior, the inner maximum over policies is attained
    (∀ μ ∈ identifiedSet u α,
      ∃ M, IsGreatest ((fun π => senderPayoff v α π μ) '' robustlyObedientPolicies u α) M) ∧
    -- max_π min_μ V = min_μ max_π V, both outer extrema attained
    (∃ w : ℝ,
      IsGreatest {x | ∃ π ∈ robustlyObedientPolicies u α,
        IsLeast ((fun μ => senderPayoff v α π μ) '' identifiedSet u α) x} w ∧
      IsLeast {x | ∃ μ ∈ identifiedSet u α,
        IsGreatest ((fun π => senderPayoff v α π μ) '' robustlyObedientPolicies u α) x} w) ∧
    -- a pure-strategy saddle point
    (∃ πs ∈ robustlyObedientPolicies u α, ∃ μs ∈ identifiedSet u α,
      ∀ π ∈ robustlyObedientPolicies u α, ∀ μ ∈ identifiedSet u α,
        senderPayoff v α π μs ≤ senderPayoff v α πs μs ∧
          senderPayoff v α πs μs ≤ senderPayoff v α πs μ) ∧
    -- for every fixed policy, the inner minimum is attained at an extreme point of P(α)
    (∀ π ∈ robustlyObedientPolicies u α,
      ∃ μhat ∈ Set.extremePoints ℝ (identifiedSet u α),
        ∀ μ ∈ identifiedSet u α, senderPayoff v α π μhat ≤ senderPayoff v α π μ) ∧
    -- in particular, every maxmin-optimal policy admits a worst-case prior in ext(P(α))
    (∀ πs ∈ robustlyObedientPolicies u α,
      (∃ m, IsLeast ((fun μ => senderPayoff v α πs μ) '' identifiedSet u α) m ∧
        IsGreatest {x | ∃ π ∈ robustlyObedientPolicies u α,
          IsLeast ((fun μ => senderPayoff v α π μ) '' identifiedSet u α) x} m) →
      ∃ μhat ∈ Set.extremePoints ℝ (identifiedSet u α),
        ∀ μ ∈ identifiedSet u α, senderPayoff v α πs μhat ≤ senderPayoff v α πs μ) := by sorry

end RobustObedientPersuasion.Saddle
