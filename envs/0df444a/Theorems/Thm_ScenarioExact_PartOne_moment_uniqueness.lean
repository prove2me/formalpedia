-- Prove2me | Theorems.Thm_ScenarioExact_PartOne_moment_uniqueness
-- name    : ScenarioExact.PartOne.moment_uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:24:51.093786+00:00
-- url     : https://prove2.me/theorems/ba1bc0a1-d6b9-4ccb-b351-24b38ad3aba6
-- title:
--   §3, PART 1, p. 8 — $F(\alpha)=\alpha^d$ is the unique solution of (3.4)
-- statement:
--   Fix an integer $d\ge1$. The identities
--   $$\binom md\int_0^1(1-\alpha)^{m-d}\,F(\mathrm d\alpha)=1,\qquad\forall m\ge d,\tag{3.4}$$
--   have exactly one solution among probability distributions $F$ on $[0,1]$, namely $F(\alpha)=\alpha^d$. Precisely:
--
--   1. **Existence.** The distribution with distribution function $\alpha^d$ on $[0,1]$, i.e. density $d\,\alpha^{d-1}$, satisfies (3.4): for every $m\ge d$,
--   $$\binom md\int_0^1(1-\alpha)^{m-d}\,d\,\alpha^{d-1}\,\mathrm d\alpha=1.$$
--   2. **Uniqueness.** If $\mu$ is a probability measure on $\mathbb R$ with $\mu(\mathbb R\setminus[0,1])=0$ and $\binom md\int_{[0,1]}(1-\alpha)^{m-d}\,\mu(\mathrm d\alpha)=1$ for every $m\ge d$, then $\mu((-\infty,\alpha])=\alpha^d$ for every $\alpha\in[0,1]$.
--
--   The paper cites the uniqueness of the solution of a moment problem for a distribution with bounded support (Shiryaev, *Probability*, Chapter II, §12.9, Corollary 1). Combined with (3.4) it gives (3.2).
--
--   **Formalization Note.** Pure measure theory, with no scenario objects. "Distribution with finite support" in the paper means a distribution supported in the bounded interval $[0,1]$, entered as $\mu([0,1]^{\mathrm c})=0$. Integrals are lower Lebesgue integrals over $[0,1]$ (as extended nonnegative reals), the same convention as (3.3) and (3.4). The hypothesis $d\ge1$ is the paper's ($d$ is the size of $x$).
-- source:
--   Campi & Garatti, The exact feasibility of randomized solutions of uncertain convex programs, SIAM J. Optim. 19(3) (2008); authors' final manuscript, p. 8, §3, PART 1, sentence after (3.4)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint
import Definitions.Def_ScenarioExact_PartOne_Basic
open MeasureTheory ScenarioApproach.Generalization
open scoped ENNReal

namespace ScenarioExact.PartOne

/-- §3, PART 1, p. 8, sentence after (3.4): `F(α) = α^d` solves (3.4), and it is the only
distribution on `[0, 1]` that does. -/
theorem moment_uniqueness {d : ℕ} (hd : 1 ≤ d) :
    -- existence: the law with density `d α^{d-1}` on `[0, 1]` (distribution function `α^d`) solves (3.4)
    (∀ m : ℕ, d ≤ m →
      (m.choose d : ℝ≥0∞) *
          ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ (m - d) * ((d : ℝ) * α ^ (d - 1))) =
        1) ∧
    -- uniqueness: every probability law on `[0, 1]` solving (3.4) has distribution function `α^d`
    ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      (∀ m : ℕ, d ≤ m →
        (m.choose d : ℝ≥0∞) * ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ (m - d)) ∂μ = 1) →
      ∀ α ∈ Set.Icc (0 : ℝ) 1, μ (Set.Iic α) = ENNReal.ofReal (α ^ d) := by sorry

end ScenarioExact.PartOne
