-- Prove2me | Theorems.Thm_StochApproxDyn_MartingaleNoise_noiseDev_block_le
-- name    : StochApproxDyn.MartingaleNoise.noiseDev_block_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:28:35.331076+00:00
-- url     : https://prove2.me/theorems/bbe96d1b-b491-4739-9e00-ed1f1cffa71e
-- title:
--   Block comparison: $\Delta(t,T)\le2\Delta(kT,T)+\Delta((k+1)T,T)$ for $kT\le t<(k+1)T$
-- statement:
--   Let $\{\gamma_n\}$ be a step sequence and $\{U_n\}_{n\ge1}$ any sequence in $\mathbb R^d$, with piecewise constant process $\bar U$ and noise deviation $\Delta(t,T)=\sup_{0\le h\le T}\|\int_t^{t+h}\bar U(s)\,ds\|$. Let $T>0$ and $k\in\mathbb N$. Then for every $t$ with $kT\le t<(k+1)T$,
--   $$\Delta(t,T)\le 2\,\Delta(kT,T)+\Delta((k+1)T,T).$$
--
--   This deterministic comparison transfers the almost sure convergence $\Delta(kT,T)\to0$ along the grid $kT$ to $\Delta(t,T)\to0$ as $t\to\infty$, which is assumption A1.
--
--   **Formalization Note** $\Delta$ takes values in $[0,\infty]$; the inequality is in $[0,\infty]$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.2, proof of Proposition 4.2, p. 16 (PDF p. 17), unnumbered display

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochApproxDyn.MartingaleNoise

/-- Benaïm 1999, §4.2, proof of Proposition 4.2, p. 16: for `kT ≤ t < (k+1)T`,
`Δ(t, T) ≤ 2Δ(kT, T) + Δ((k+1)T, T)`. Deterministic: `U` is any sequence and `γ` any step
sequence satisfying the standing assumptions of §4.1. -/
theorem noiseDev_block_le {d : ℕ} (γ : ℕ → ℝ) (hγ : IsStepSequence γ)
    (U : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℝ) (hT : 0 < T) (k : ℕ) (t : ℝ)
    (hkt : (k : ℝ) * T ≤ t) (htk : t < ((k : ℝ) + 1) * T) :
    noiseDev γ U t T ≤ 2 * noiseDev γ U ((k : ℝ) * T) T + noiseDev γ U (((k : ℝ) + 1) * T) T := by sorry

end StochApproxDyn.MartingaleNoise
