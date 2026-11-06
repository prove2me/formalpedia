-- Prove2me | Theorems.Thm_PolarizedLearning_mlProjection_eq
-- name    : PolarizedLearning.mlProjection_eq
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:18:53.010781+00:00
-- url     : https://prove2.me/theorems/bcc38e97-281a-4707-a454-91dbcc06632d
-- title:
--   Eq. (5), p. 12 — the ML beliefs are $\Pi(x)=[\mathrm{proj}_{[0,1]}(a^-(x)),\mathrm{proj}_{[0,1]}(a^+(x))]$
-- statement:
--   Fix the model parameters and an ML statistic $x\in[0,1]$. Let $B(x)$ be the set of maximizers over $B_0=[0,1]\times[u-\epsilon,u+\epsilon]$ of the normalized log-likelihood $\tilde\ell(x;\tilde\pi,\tilde u)=x\log\theta+(1-x)\log(1-\theta)$, $\theta=L+(H-L)\tilde\pi+p(2\tilde u-1)$, and let $\Pi(x)$ be its projection onto the $\tilde\pi$-coordinate. Put
--   $$a^-(x)=\frac{x-L-p(2(u+\epsilon)-1)}{H-L},\qquad a^+(x)=\frac{x-L-p(2(u-\epsilon)-1)}{H-L},$$
--   the right-hand side of (5) at $\tilde u=u+\epsilon$ and $\tilde u=u-\epsilon$. Then $B(x)$ is nonempty and
--   $$\Pi(x)=\bigl[\mathrm{proj}_{[0,1]}(a^-(x)),\ \mathrm{proj}_{[0,1]}(a^+(x))\bigr],$$
--   so $\pi^-(x)=\mathrm{proj}_{[0,1]}(a^-(x))$ and $\pi^+(x)=\mathrm{proj}_{[0,1]}(a^+(x))$.
--
--   This makes precise the paper's remark that the ML estimates form a line segment from $(\pi^-,u^-)$ to $(\pi^+,u^+)$, and gives the continuity of $\pi^\pm$ in $x$ that the convergence argument uses.
--
--   Differences from the source:
--   - reading: (5) holds at every ML estimate; 'This implies that B_t is a line segment from (π−t,u−t) to (π+t,u+t)' → B(x) nonempty and Π(x) equals the interval between (5) clipped at ũ = u + ϵ and at ũ = u − ϵ; reason: (5) is only a necessary condition; the segment's ends are where ũ is extreme, as the paper's Figure 1 and Cases (iv)–(v) on pp. ec3–ec4 use
--   - encoding: B_t from ℓ_t(n_t; ·) → B(x) from ℓ̃(x; ·) at x = n_t/t (p. ec1); reason: ℓ_t(tx; ·) = t·ℓ̃(x; ·), same maximizers for t ≥ 1 (checked in Lean)
--   - reading: standing assumptions of pp. 8–11 (H > L, p > 0, L − p > 0, H + p < 1, u ∈ (0,1), [u−ϵ,u+ϵ] ⊆ [0,1], α > 0.5) → Params, which also requires ϵ > 0 and α < 1; reason: ϵ is called a degree of uncertainty and divided by on p. 17; the signal 'noisily reveals' quality (p. 11), and at α = 1 learning is complete (counterexample in paper.md item 3)
-- source:
--   Kadiyala–Shin, Social Learning and Content Quality under Polarization, MSOM (2024), doi:10.1287/msom.2022.0533, §3.4, eq. (5) and the sentence after it, p. 12 (PDF 12); e-companion, (EC.2), p. ec1 (PDF 33)

import Mathlib
import Definitions.Def_PolarizedLearning_Model

namespace PolarizedLearning

/-- **The ML beliefs form the interval between the clipped first-order conditions at `ũ = u ± ϵ`**,
Kadiyala–Shin, *Social Learning and Content Quality under Polarization*, MSOM (2024),
doi:10.1287/msom.2022.0533, eq. (5) and the sentence after it, p. 12 (PDF 12); (EC.2), p. ec1
(PDF 33).

For `x ∈ [0,1]`, the ML set `B(x)` is nonempty and
`Π(x) = [proj_{[0,1]}(a⁻(x)), proj_{[0,1]}(a⁺(x))]`, where
`a⁻(x) = (x − L − p(2(u+ϵ) − 1)) / (H − L)` and `a⁺(x) = (x − L − p(2(u−ϵ) − 1)) / (H − L)`
are (5) evaluated at `ũ = u + ϵ` and `ũ = u − ϵ`. Hence `π⁻(x) = proj_{[0,1]}(a⁻(x))` and
`π⁺(x) = proj_{[0,1]}(a⁺(x))`. -/
theorem mlProjection_eq (P : Params) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (mlSet P x).Nonempty ∧
    Pi P x = Set.Icc (proj01 ((x - P.L - P.p * (2 * (P.u + P.eps) - 1)) / (P.H - P.L)))
      (proj01 ((x - P.L - P.p * (2 * (P.u - P.eps) - 1)) / (P.H - P.L))) ∧
    piMinus P x = proj01 ((x - P.L - P.p * (2 * (P.u + P.eps) - 1)) / (P.H - P.L)) ∧
    piPlus P x = proj01 ((x - P.L - P.p * (2 * (P.u - P.eps) - 1)) / (P.H - P.L)) := by sorry

end PolarizedLearning
