-- Prove2me | Theorems.Thm_RandGraphStates_Supplement_theorem_2_2
-- name    : RandGraphStates.Supplement.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:21:55.245978+00:00
-- url     : https://prove2.me/theorems/f2bc2abd-ece5-4979-97c7-17fc2222d13a
-- title:
--   Theorem 2.2, p.5 — for constant $p$, whp $\delta_{\mathrm{LC}}(G_{n,p})=\theta(p)n+o(n)$
-- statement:
--   Let $H(x)=-x\log_2x-(1-x)\log_2(1-x)$ be the entropy function, let $\theta_0\in(0,1)$ be the real number with
--   $$
--   1-H(\theta_0)=\theta_0\log_2 3
--   $$
--   ($\theta_0\approx0.1893$), and let $\theta(p)=\min\{p,\,2p(1-p),\,\theta_0\}$. Let $p\in(0,1)$ be a constant and let $G_{n,p}$ be the Erdős–Rényi random graph on $n$ labelled vertices, each edge present independently with probability $p$. Then with high probability
--   $$
--   \delta_{\mathrm{LC}}(G_{n,p})=\theta(p)\cdot n+o(n),
--   $$
--   that is, for every $\varepsilon>0$,
--   $$
--   \Pr\bigl(|\delta_{\mathrm{LC}}(G_{n,p})-\theta(p)n|\le\varepsilon n\bigr)\to1\qquad(n\to\infty).
--   $$
--
--   The function $\theta$ has a plateau at $\theta_0$ for $p$ between $\theta_0$ and $\frac{1+\sqrt{1-2\theta_0}}2\approx0.8942$: over this range the typical distance of a random graph state does not depend on $p$. At $p=1/2$ the theorem recovers the lower bound $\delta_{\mathrm{LC}}\ge0.189n$ known for some graphs.
--
--   **Formalization Note** $H$ is the published binary entropy in bits `SquashedKey.h₂` and $\log_23$ is `Real.logb 2 3`. $\theta_0$ is bound by its equation on $(0,1)$, which has exactly one solution there. $G_{n,p}$ is the published `gnpProb`.
--
--   Differences from the source:
--   - encoding: θ0 ∈ (0, 1) the real number with 1 − H(θ0) = θ0 log₂ 3 → every θ0 ∈ (0, 1) satisfying the equation; reason: the solution in (0, 1) is unique, so this is the printed constant; its existence is proved in the sanity file
--   - encoding: with high probability δLC(Gn,p) = θ(p)n + o(n) → for every ε > 0, Pr(|δLC(G) − θ(p)n| ≤ εn) → 1; reason: the standard unfolding of whp with an o(n) error, two-sided
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Theorem 2.2, p.5; θ0 and θ(p) on p.4, display (1); proof §3.2, pp.11–17

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting
import Definitions.Def_SquashedKey_KeyBoundFunction
import Definitions.Def_RandGraphStates_alphaLC
import Definitions.Def_RandGraphStates_Supplement_deltaLC

set_option autoImplicit false

open BollobasChromatic.Main
open Filter Topology

namespace RandGraphStates.Supplement

/-- **Theorem 2.2.** Let `p ∈ (0, 1)` be constant. Then with high probability
`δLC(G_{n,p}) = θ(p) · n + o(n)`, where `θ(p) = min{p, 2p(1 - p), θ₀}` and `θ₀ ∈ (0, 1)` is the
real number such that `1 - H(θ₀) = θ₀ log₂ 3`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript
(November 2026), Theorem 2.2, p.5; `θ₀` and `θ(p)` from p.4, display (1).

**Formalization Note.** `H` is the entropy function in bits, the published `SquashedKey.h₂`;
`log₂ 3` is `Real.logb 2 3`. `θ₀` is bound by its equation on `(0, 1)`, which has exactly one
solution there (`x ↦ 1 - H(x) - x log₂ 3` is convex, `1` at `0` and `1 - log₂ 3 < 0` at `1`), so
this is the printed constant. `θ(p)` is written with the `min` formula of p.4. `G_{n,p}` is the
published `gnpProb`; "with high probability" is probability `→ 1`; the `o(n)` is unfolded to every
fixed `ε > 0`, two-sided: `|δLC(G) - θ(p)n| ≤ εn`. `p` is fixed before `n`. -/
theorem theorem_2_2 :
    ∀ θ0 : ℝ, 0 < θ0 → θ0 < 1 → 1 - SquashedKey.h₂ θ0 = θ0 * Real.logb 2 3 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => gnpProb n p (fun G =>
          |(deltaLC G : ℝ) - min (min p (2 * p * (1 - p))) θ0 * n| ≤ ε * n))
        atTop (𝓝 1) := by sorry

end RandGraphStates.Supplement
