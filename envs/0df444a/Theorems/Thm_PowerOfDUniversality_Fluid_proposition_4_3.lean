-- Prove2me | Theorems.Thm_PowerOfDUniversality_Fluid_proposition_4_3
-- name    : PowerOfDUniversality.Fluid.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:29.584227+00:00
-- url     : https://prove2.me/theorems/cc0c2863-c148-43c0-9c4c-42f13fadc213
-- title:
--   Proposition 4.3 — the scaled JSQ martingales (1/N)Σ_i(|M_{A,i}| + |M_{D,i}|) vanish, uniformly on compacts in probability
-- statement:
--   Consider the ordinary JSQ policy in systems with $N_j\ge 1$ servers, $N_j\to\infty$, buffer $b\ge 1$ and arrival rates $\lambda_j\ge 0$ with $\lambda_j/N_j\to\lambda>0$, whose random initial states satisfy $\mathbf q^{N_j}(0)\to\mathbf q^\infty\in\mathcal S$ in probability in $\ell_1$. Let $A_i(t)$ be the number of arrivals in $[0,t]$ assigned to a server with $i-1$ tasks, $D_i(t)$ the number of departures from a server with $i$ tasks, and
--   $$M_{A,i}(t)=A_i(t)-\lambda_j\int_0^t p_{i-1}(\mathbf Q(s))\,ds,\qquad M_{D,i}(t)=D_i(t)-\int_0^t\big(Q_i(s)-Q_{i+1}(s)\big)\,ds,$$
--   where $p_{i-1}(\mathbf Q)=1$ if the shortest queue holds exactly $i-1$ tasks and $0$ otherwise. Then
--   $$\Big\{\frac1{N_j}\sum_{i\ge 1}\big(|M_{A,i}(t)|+|M_{D,i}(t)|\big)\Big\}_{t\ge0}\xrightarrow{\ \mathcal L\ }0 .$$
--
--   This is the step that makes the martingale part of the representation (4.9) negligible in $\ell_1$ on the fluid scale.
--
--   **Formalization Note** Convergence in distribution to the zero process is stated in its equivalent form: for every $T\ge 0$ and $\varepsilon>0$, $\mathbb P\big(\sup_{t\in[0,T]}\frac1{N_j}\sum_{i=1}^{b}(|M_{A,i}(t)|+|M_{D,i}(t)|)\ge\varepsilon\big)\to 0$. The standing assumptions of §4.1 (those of Theorem 4.1) are hypotheses. The martingales are defined from the counts, which agrees pathwise with (4.8); the sum is taken in $[0,\infty]$.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, pp. 17–18, Proposition 4.3, (4.6), (4.8)

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-- **Proposition 4.3** (p. 18, convergence of martingales), under the standing assumptions of
Theorem 4.1 (`N_j → ∞` servers, `λ_j / N_j → λ > 0`, `q^{N_j}(0) → q^∞ ∈ 𝕊` in probability in
`ℓ¹`, ordinary JSQ). The process `(1/N) ∑_{i≥1} (|M^N_{A,i}(t)| + |M^N_{D,i}(t)|)` converges in
distribution to the zero process; since the limit is deterministic and continuous this is
locally uniform convergence in probability: for all `T ≥ 0` and `ε > 0`,
`P(sup_{t ∈ [0,T]} (1/N) ∑_{i≥1} (|M^N_{A,i}(t)| + |M^N_{D,i}(t)|) ≥ ε) → 0`. -/
theorem proposition_4_3 (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam : 0 < lam)
    (Ns : ℕ → ℕ) (hNs1 : ∀ j, 1 ≤ Ns j) (hNs : Tendsto Ns atTop atTop)
    (lamN : ℕ → ℝ) (hlamN : ∀ j, 0 ≤ lamN j)
    (hlim : Tendsto (fun j => lamN j / (Ns j : ℝ)) atTop (𝓝 lam))
    (qinf : ℕ → ℝ) (hqinf : qinf ∈ FluidSpace b)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (sys : ∀ j, System P (Ns j) b (lamN j))
    (hinit : ∀ ε : ℝ, 0 < ε → Tendsto (fun j => P {ω | ENNReal.ofReal ε ≤
      l1dist (scaledOcc (Ns j) ((sys j).Q0 ω)) qinf}) atTop (𝓝 0)) :
    ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun j => P {ω | ENNReal.ofReal ε ≤
        ⨆ (t : ℝ) (_ : t ∈ Set.Icc 0 T), (sys j).jsqMartNorm ω t}) atTop (𝓝 0) := by sorry

end PowerOfDUniversality.Fluid
