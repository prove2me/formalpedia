-- Prove2me | Theorems.Thm_SluggishCapability_Myopic_step_3
-- name    : SluggishCapability.Myopic.step_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:48.93516+00:00
-- url     : https://prove2.me/theorems/f5d3f991-2f9d-4ae6-b6e0-9bf1d2d0f0b7
-- title:
--   Step 3, pp. 19–20, with ε < 1/2 (corrected argument) — every invariant law charges a capability ≤ 2µ − 1
-- statement:
--   Let $\mu \ge 1$ be an integer and $0 < \varepsilon < 1/2$. Let $(P, f)$ be a feasible training program on a finite set $S$, $M \ge \max_s f(s)$, and $\nu$ an invariant distribution of the extended (capability, state) chain. Then $\nu$ charges some state of capability at most $2\mu - 1$:
--   $$\exists\,(m, s):\quad \nu(m, s) > 0 \ \text{ and } \ m \le 2\mu - 1 .$$
--
--   Since every invariant distribution is supported on recurrent states, this says that the minimal long-run capability is at most $2\mu - 1$, Step 3 of the paper.
--
--   **Formalization Note** The hypothesis $\varepsilon < 1/2$ is added: for $\varepsilon > 1/2$ the claim is false (with $\mu = 1$, $\varepsilon = 3/5$, $P = \begin{pmatrix}0 & 1\\ 7/8 & 1/8\end{pmatrix}$, $f(L) = 0$, $f(H) = 3$, the average challenge is $8/5 = \mu + \varepsilon$ and the only invariant law lives on capabilities $2$ and $3$). The paper's printed argument (average at most about $2\mu$, distribution non-degenerate) only yields a minimum at most $2\mu$; a proof must supply the step to $2\mu - 1$. $2\mu - 1$ is natural-number subtraction, harmless since $\mu \ge 1$.
-- source:
--   Eliaz, Spiegler, Capability Building in Sluggish Organizations, authors' manuscript of March 28, 2022 (Management Science 2023, doi:10.1287/mnsc.2022.4445), pp. 19–20, Step 3 of the proof of Proposition 1(i)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting

open MarkovMixing

namespace SluggishCapability.Myopic

/-- Step 3, pp. 19–20, in stationary form and with `ε < 1/2` added: every invariant distribution
of the extended chain of a feasible program charges some state whose capability is at most
`2µ − 1` (natural-number subtraction; `2µ − 1 ≥ 1` since `µ ≥ 1`). -/
theorem step_3 (μ : ℕ) (hμ : 1 ≤ μ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hεhalf : ε < 1 / 2)
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (f : S → ℕ) (hfeas : IsFeasibleProgram P f μ ε)
    (M : ℕ) (hM : ∀ s, f s ≤ M)
    (ν : Fin (M + 1) × S → ℝ) (hν : IsStationary (extKernel P f M) ν) :
    ∃ x : Fin (M + 1) × S, 0 < ν x ∧ (x.1 : ℕ) ≤ 2 * μ - 1 := by sorry

end SluggishCapability.Myopic
