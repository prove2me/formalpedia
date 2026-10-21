-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_theorem_1
-- name    : SWSSNet.Diffusion.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:58.725603+00:00
-- url     : https://prove2.me/theorems/52e05581-4765-42dc-a409-8760dc845016
-- title:
--   Theorem 1 (limiting diffusion) — ϑ_p > 0: exponentially ergodic under v̄; ϑ_p < 0: transient, ϑ_p = 0: no invariant law, under every Markov control
-- statement:
--   Consider a multiclass multi-pool parallel-server network whose class–pool graph is a tree, in the Halfin–Whitt regime without abandonment, under complete resource pooling. Let $p$ be a positive probability vector and $\vartheta_p$ the SWSS parameter, the optimal value of (LP′). Let
--   $$
--   dX_t=b(X_t,U_t)\,dt+\Sigma\,dW_t \qquad (41)
--   $$
--   be the limiting controlled diffusion, with drift (42) built from $h$ of (12) and $\Sigma=\mathrm{diag}(\sqrt{2\lambda_i})$.
--
--   **(a)** Suppose $\vartheta_p>0$. Let $(\hat\imath,\hat\jmath)$ be any edge, and consider the stationary Markov control $\bar v\equiv(e_{\hat\imath},e_{\hat\jmath})$ (all queued jobs in class $\hat\imath$, all idle servers in pool $\hat\jmath$). Then:
--
--   1. strong solutions exist from every initial point;
--   2. their transition probability $P_t(x,\cdot)$ has a unique invariant probability measure $\pi$;
--   3. there are a centre $c\in\mathbb R^I$, a positive definite $S$ and $\varepsilon>0$ such that, with $V(x)=V_{\varepsilon,S}(x-c)$:
--      - $\int V\,d\pi<\infty$ (exponential tails);
--      - there are $C,\gamma>0$ with
--   $$
--   \|P_t(x,\cdot)-\pi\|_V\le C\,V(x)\,e^{-\gamma t}\qquad\forall x,\ t\ge0 .
--   $$
--
--   **(b)** If $\vartheta_p<0$, the diffusion is transient under every stationary Markov control: every strong solution, from every initial point, satisfies $|X_t|\to\infty$ a.s. If $\vartheta_p=0$, under every stationary Markov control the transition probability of the strong solutions has no invariant probability measure.
--
--   The sign of a single linear-program value thus decides whether the limiting diffusion can be stabilized.
--
--   **Formalization Note** Only the limiting-diffusion clauses of Theorem 1 are posed. The clauses about the diffusion-scaled $n$th systems (Theorems 6 and 8 of the paper) need a controlled continuous-time Markov chain layer. Part (a) is stated for every edge's constant control, which is what the paper proves (Theorem 7 with Remark 8), and is stronger than "some stationary Markov control". The centre $c$ comes from the recentring of Remark 8. "Transient" is $|X_t|\to\infty$ a.s.; "cannot be positive recurrent" is the absence of an invariant probability measure. Weighted norms are the published `tvNormWeighted` (weight $1+V$, equivalent to the $V$-norm up to a factor $2$).
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 9, Theorem 1 (limiting-diffusion clauses; proved by Theorems 5 and 7 and Remark 8)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov
import Definitions.Def_SWSSNet_Diffusion_Network
import Definitions.Def_SWSSNet_Diffusion_Process

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSNet.Diffusion

/-- Theorem 1, p. 9 (limiting-diffusion clauses): (a) if `ϑ_p > 0`, then for every edge `(î, ĵ)`
the limiting diffusion (41)–(42) under the constant stationary Markov control `v̄ = (e_î, e_ĵ)` has
strong solutions and a transition probability with a unique invariant probability measure `π`, which
has exponential tails, and is exponentially ergodic in the norm weighted by
`V(x) = V_{ε,S}(x − c)`; (b) if `ϑ_p < 0` it is transient under every stationary Markov control, and
if `ϑ_p = 0` it has no invariant probability measure under any stationary Markov control. -/
theorem theorem_1 {I J : ℕ} (N : TreeNetwork I J) (p : Fin I → ℝ) (hp : IsPosProb p) :
    (0 < swss N p → ∀ (î : Fin I) (ĵ : Fin J), N.adj î ĵ →
      HasStrongSolutions (markovDrift N (hvec N) (fun _ => constCtrl î ĵ)) (Sigma N) ∧
      ∃ P : ℝ≥0 → EthierKurtz.SDEState I → Measure (EthierKurtz.SDEState I),
        IsStrongTransition (markovDrift N (hvec N) (fun _ => constCtrl î ĵ)) (Sigma N) P ∧
        ∃ π : Measure (EthierKurtz.SDEState I), GPhNGIDiffusion.EMError.IsInvariantMeasure P π ∧
          (∀ π', GPhNGIDiffusion.EMError.IsInvariantMeasure P π' → π' = π) ∧
          ∃ (c : EthierKurtz.SDEState I) (S : Matrix (Fin I) (Fin I) ℝ) (ε : ℝ), S.PosDef ∧ 0 < ε ∧
            (∫⁻ y, ENNReal.ofReal (lyapVS ε S (y - c)) ∂π) < ⊤ ∧
            ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ (t : ℝ≥0) (x : EthierKurtz.SDEState I),
              GPhNGIDiffusion.EMError.tvNormWeighted (fun y => lyapVS ε S (y - c)) (P t x) π
                ≤ ENNReal.ofReal (C * lyapVS ε S (x - c) * Real.exp (-γ * t))) ∧
    (swss N p < 0 → ∀ v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ), IsMarkovControl v →
      IsTransient (markovDrift N (hvec N) v) (Sigma N)) ∧
    (swss N p = 0 → ∀ v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ), IsMarkovControl v →
      ∀ P : ℝ≥0 → EthierKurtz.SDEState I → Measure (EthierKurtz.SDEState I),
        IsStrongTransition (markovDrift N (hvec N) v) (Sigma N) P →
        ¬ ∃ π, GPhNGIDiffusion.EMError.IsInvariantMeasure P π) := by sorry

end SWSSNet.Diffusion
