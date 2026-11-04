-- Prove2me | Theorems.Thm_RetirePartialInfo_Duality_optional_sampling_Zv
-- name    : RetirePartialInfo.Duality.optional_sampling_Zv
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T06:41:20.33736+00:00
-- url     : https://prove2.me/theorems/dbe42379-20dc-4f3e-8bd6-1fbdd4496da9
-- title:
--   Optional sampling for the projected density: $\tilde E[g(\tau)]=E[\mathcal Z_\tau g(\tau)]$ at an $\mathcal F^S$-retirement time
-- statement:
--   Optional sampling for the projected density at a retirement time. Assume the set-up of §2.1, that $\int_0^\cdot\theta\,dW$ is the Itô integral defining $Z$ in (3), Assumption 2.1, and that $\mathcal Z$ is a continuous positive version of the projected density $\mathcal Z_t=E[Z_T\mid\mathcal F^S_t]$ of (6). Let $\tau$ be an $\mathcal F^S$-stopping time with values in $[0,T_1]$ and let $g:\mathbb R\to\mathbb R$ be continuous. Then the stopped density $\mathcal Z_\tau$ is $P$-integrable and
--   $$\tilde E[g(\tau)]=E[Z_T\,g(\tau)]=E[\mathcal Z_\tau\,g(\tau)].$$
--
--   This is the optional sampling identity $E[Z_T\mid\mathcal F^S_\tau]=\mathcal Z_\tau$ for the $P$-martingale $\mathcal Z$, applied to the $\mathcal F^S_\tau$-measurable bounded variable $g(\tau)$. The paper uses it implicitly when it rewrites the retirement term of the budget constraint (8), $\tilde E[\int b(u)/B_u\,dR_u]$, as the dual term $E[e^{-\beta\tau}y_\tau b(\tau)]$ of (14), and in the budget cost (17)–(21).
--
--   **Formalization Note.** $\tilde P=Z_T\cdot P$ enters through $E[Z_T\,g(\tau)]$. The retirement time is encoded as in `IsRetirementTime` ($\tau\le T_1\le T$); `Zv` is the continuous positive version of `IsZVersion`.
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), pp. 11–13, passage from (8) and (13) to (14) and (17)–(21) (optional sampling for 𝒵 at the retirement time); cf. Karatzas–Shreve, Brownian Motion and Stochastic Calculus, Theorem 1.3.22

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility
import Definitions.Def_RetirePartialInfo_Duality_Primal

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RetirePartialInfo.Duality

/-- **Optional sampling for the projected density at a retirement time** (used in the passage from
(13) to (14) and in (17)–(21), pp. 11–13 of Chen, Jeon, Wong, Optimal retirement under partial
information, SSRN 3683553 (version of June 8, 2021); standard optional sampling, cf. Karatzas–Shreve,
Brownian Motion and Stochastic Calculus, Thm. 1.3.22): for an `F^S`-stopping time `τ ∈ [0, T1]` and a
continuous `g`, the stopped density `𝒵_τ` is integrable and `Ẽ[g(τ)] = E[Z_T g(τ)] = E[𝒵_τ g(τ)]`. -/
theorem optional_sampling_Zv {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ Zv : ℝ≥0 → Ω → ℝ) (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ)
    (h21 : Assumption21 p st Iθ) (hZv : IsZVersion p st Iθ Zv)
    (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ) (g : ℝ → ℝ) (hg : Continuous g) :
    Integrable (fun ω => Zv (τ ω) ω) st.P ∧
      ∫ ω, Z p st Iθ p.Tn ω * g (τ ω) ∂st.P = ∫ ω, Zv (τ ω) ω * g (τ ω) ∂st.P := by sorry

end RetirePartialInfo.Duality
