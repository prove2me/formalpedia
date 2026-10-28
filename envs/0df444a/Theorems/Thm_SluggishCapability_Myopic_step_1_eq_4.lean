-- Prove2me | Theorems.Thm_SluggishCapability_Myopic_step_1_eq_4
-- name    : SluggishCapability.Myopic.step_1_eq_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:32.331387+00:00
-- url     : https://prove2.me/theorems/35b6df51-c7da-42e0-9493-01c2d220c6e0
-- title:
--   Step 1, eq. (4), p. 18 — Σ over X⁺ of λ(m,d)(m+1) equals Σ over X⁻ of λ(m,d)m
-- statement:
--   Let $P$ be stochastic on a finite set $S$, $f : S \to \mathbb{N}$, $M \ge \max_s f(s)$, and let $\nu$ be an invariant distribution of the extended chain on pairs $(m, s)$. For a state $(m, s)$ and a next trainer state $s'$, the pair $(m_t, d_{t+1}) = (m, f(s'))$ has long-run frequency
--   $$\lambda(m, s, s') = \nu(m, s)\, P(s, s').$$
--   The pair is in $X^+$ if $d > m$ and in $X^-$ if $d < m$. Then, with $d = f(s')$,
--   $$\sum_{d > m} \lambda(m, s, s')\,(m + 1) \;=\; \sum_{d < m} \lambda(m, s, s')\, m. \tag{4}$$
--
--   Equation (4) balances the upward and downward moves of capability; it is the first step of the proof of Proposition 1(i).
--
--   **Formalization Note** The paper's pairs are $(m_{t-1}, d_t)$; here the chain state is $(m_t, s_t)$ and the weight $\nu(m,s)P(s,s')$ is the frequency of $(m_t, d_{t+1})$, the same pair shifted by one period.
-- source:
--   Eliaz, Spiegler, Capability Building in Sluggish Organizations, authors' manuscript of March 28, 2022 (Management Science 2023, doi:10.1287/mnsc.2022.4445), p. 18, Step 1, eq. (4) (X⁺, X⁻ defined on p. 17)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting

open MarkovMixing

namespace SluggishCapability.Myopic

/-- Step 1, eq. (4), p. 18. Let `ν` be an invariant distribution of the extended chain. The
long-run frequency of the pair `(m_t, d_{t+1}) = (x.1, f s')` is `ν x * P x.2 s'`; the pair is in
`X⁺` when `d > m` and in `X⁻` when `d < m`. Then
`∑_{X⁺} λ(m, d) (m + 1) = ∑_{X⁻} λ(m, d) m`. -/
theorem step_1_eq_4 {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (f : S → ℕ) (M : ℕ) (hP : IsStochastic P) (hM : ∀ s, f s ≤ M)
    (ν : Fin (M + 1) × S → ℝ) (hν : IsStationary (extKernel P f M) ν) :
    ∑ x : Fin (M + 1) × S, ∑ s' : S,
        (if (x.1 : ℕ) < f s' then ν x * P x.2 s' * ((x.1 : ℝ) + 1) else 0) =
      ∑ x : Fin (M + 1) × S, ∑ s' : S,
        (if f s' < (x.1 : ℕ) then ν x * P x.2 s' * (x.1 : ℝ) else 0) := by sorry

end SluggishCapability.Myopic
