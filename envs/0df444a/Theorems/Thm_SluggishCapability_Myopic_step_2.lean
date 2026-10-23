-- Prove2me | Theorems.Thm_SluggishCapability_Myopic_step_2
-- name    : SluggishCapability.Myopic.step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:46.121094+00:00
-- url     : https://prove2.me/theorems/11e7ab30-7b4b-4263-828d-31c49768e890
-- title:
--   Step 2, pp. 18–19 — the long-run average capability is at most 2(µ + ε) − Σ over X⁰ of λ(m,d)m
-- statement:
--   Let $\mu \ge 1$ be an integer and $\varepsilon \in (0,1)$. Let $(P, f)$ be a feasible training program on a finite set $S$, $M \ge \max_s f(s)$, and $\nu$ an invariant distribution of the extended chain. With the pair frequencies $\lambda(m,s,s') = \nu(m,s)P(s,s')$ of $(m_t, d_{t+1}) = (m, f(s'))$ and $X^0$ the pairs with $d = m$,
--   $$\mathbb{E}(m) = \sum_{(m,s)} \nu(m,s)\, m \;\le\; 2(\mu + \varepsilon) - \sum_{d = m} \lambda(m, s, s')\, m .$$
--
--   The paper writes this as $\mathbb{E}(m) \lessapprox 2\mu - \sum_{X^0}\lambda(m,d)m \le 2\mu$, treating $\varepsilon$ as negligible; the statement here keeps $\varepsilon$ explicitly.
-- source:
--   Eliaz, Spiegler, Capability Building in Sluggish Organizations, authors' manuscript of March 28, 2022 (Management Science 2023, doi:10.1287/mnsc.2022.4445), pp. 18–19, Step 2 (eq. (5) and the display ending Step 2)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting

open MarkovMixing

namespace SluggishCapability.Myopic

/-- Step 2, pp. 18–19. For a feasible program and an invariant distribution `ν` of the extended
chain, the long-run average capability satisfies
`E(m) ≤ 2(µ + ε) − ∑_{(m,d) ∈ X⁰} λ(m, d) m`, where `X⁰` is the set of pairs
`(m_t, d_{t+1}) = (x.1, f s')` with `d = m`, of frequency `ν x * P x.2 s'`. -/
theorem step_2 (μ : ℕ) (hμ : 1 ≤ μ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (f : S → ℕ) (hfeas : IsFeasibleProgram P f μ ε)
    (M : ℕ) (hM : ∀ s, f s ≤ M)
    (ν : Fin (M + 1) × S → ℝ) (hν : IsStationary (extKernel P f M) ν) :
    ∑ x : Fin (M + 1) × S, ν x * (x.1 : ℝ) ≤
      2 * ((μ : ℝ) + ε) - ∑ x : Fin (M + 1) × S, ∑ s' : S,
        (if f s' = (x.1 : ℕ) then ν x * P x.2 s' * (x.1 : ℝ) else 0) := by sorry

end SluggishCapability.Myopic
