-- Prove2me | Theorems.Thm_StochApproxDyn_SubgaussianNoise_noiseDev_block_le
-- name    : StochApproxDyn.SubgaussianNoise.noiseDev_block_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T00:46:08.722056+00:00
-- url     : https://prove2.me/theorems/9d8349e4-b252-4c0a-806a-9b55784bb331
-- title:
--   Block comparison: $\Delta(t,T)\le2\Delta(kT,T)+\Delta((k+1)T,T)$ for $kT\le t<(k+1)T$
-- statement:
--   Let $\{\gamma_n\}$ be a step sequence and $\{U_n\}_{n\ge1}$ any sequence in $\mathbb R^d$, with piecewise constant process $\bar U$ and noise deviation $\Delta(t,T)=\sup_{0\le h\le T}\|\int_t^{t+h}\bar U(s)\,ds\|$. Let $T>0$ and $k\in\mathbb N$. Then for every $t$ with $kT\le t<(k+1)T$,
--   $$\Delta(t,T)\le 2\,\Delta(kT,T)+\Delta((k+1)T,T).$$
--
--   This deterministic comparison transfers the almost sure convergence $\Delta(kT,T)\to0$ along the grid $kT$ to $\Delta(t,T)\to0$ as $t\to\infty$, which is assumption A1. The proof of Proposition 4.4 ends with this step ("the end of the proof is now exactly as in proposition 4.2").
--
--   **Formalization Note** $\Delta$ takes values in $[0,\infty]$; the inequality is in $[0,\infty]$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.2, proof of Proposition 4.2, p. 16 (PDF p. 17), unnumbered display; invoked in the proof of Proposition 4.4, p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochApproxDyn.SubgaussianNoise

/-- Benaïm 1999, §4.2, proof of Proposition 4.2, p. 16 (invoked in the proof of Proposition 4.4, p. 17): for `kT ≤ t < (k+1)T`,
`Δ(t, T) ≤ 2Δ(kT, T) + Δ((k+1)T, T)`. Deterministic: `U` is any sequence and `γ` any step
sequence satisfying the standing assumptions of §4.1. -/
theorem noiseDev_block_le {d : ℕ} (γ : ℕ → ℝ) (hγ : StochApproxDyn.MartingaleNoise.IsStepSequence γ)
    (U : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℝ) (hT : 0 < T) (k : ℕ) (t : ℝ)
    (hkt : (k : ℝ) * T ≤ t) (htk : t < ((k : ℝ) + 1) * T) :
    StochApproxDyn.MartingaleNoise.noiseDev γ U t T ≤ 2 * StochApproxDyn.MartingaleNoise.noiseDev γ U ((k : ℝ) * T) T + StochApproxDyn.MartingaleNoise.noiseDev γ U (((k : ℝ) + 1) * T) T := by sorry

end StochApproxDyn.SubgaussianNoise
