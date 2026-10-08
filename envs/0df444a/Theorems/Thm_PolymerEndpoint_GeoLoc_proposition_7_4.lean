-- Prove2me | Theorems.Thm_PolymerEndpoint_GeoLoc_proposition_7_4
-- name    : PolymerEndpoint.GeoLoc.proposition_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:34:24.946428+00:00
-- url     : https://prove2.me/theorems/f0346138-4981-44dd-b5f7-fdcc92e2bae3
-- title:
--   Proposition 7.4, p. 50 — under (7.4) the endpoint localizes in the favourite region 𝒞_i^K (7.9)
-- statement:
--   For $i\ge0$ and $K\ge0$ let $\mathcal C_i^K$ be the set of all $x\in\mathbb Z^d$ within $\ell^1$ distance $K$ of every mode of the endpoint probability mass function $f_i$. Let $d\ge1$, $\mathfrak L$ non-degenerate with (1.1), $\beta>\beta_c$, and assume the single-copy condition (7.4). Then
--   $$\lim_{K\to\infty}\liminf_{n\to\infty}\frac1n\sum_{i=0}^{n-1}\rho_i(\omega_i\in\mathcal C_i^K)=1\quad\text{a.s.}\qquad(7.9)$$
--
--   This is the Cesàro form of the favourite-region localization proved by Comets and Nguyen for the log-gamma polymer, here conditional on (7.4).
--
--   **Formalization Note.** (7.4) is stated over $\mathcal M$ at a low temperature; the hypothesis $\beta>\beta_c$, implicit in (7.4) (Theorem 7.3(b)), is made explicit. The limit $K\to\infty$ is taken along integers; the inner $\liminf$ is non-decreasing in $K$, so this is the same limit.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 50, Proposition 7.4, (7.9); p. 49, (7.4)

import Mathlib
import Definitions.Def_PolymerEndpoint_GeoLoc_Update
import Definitions.Def_PolymerEndpoint_GeoLoc_Functionals
open MeasureTheory ProbabilityTheory Filter Topology

namespace PolymerEndpoint.GeoLoc

/-- Proposition 7.4: under the single-copy condition (7.4) (with `β > β_c`), the endpoint is
localized in the favourite region `𝒞_i^K` in the Cesàro sense (7.9). -/
theorem proposition_7_4 (d : ℕ) (hd : 1 ≤ d) (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (h𝔏 : ∀ c : ℝ, 𝔏 ≠ Measure.dirac c) (β : ℝ) (hβ : 0 ≤ β)
    (hmgf : ∀ α ∈ Set.Icc (-2 * β) (2 * β), Integrable (fun x => Real.exp (α * x)) 𝔏)
    (hlow : LowTemp d 𝔏 β)
    (hsingle : ∀ ν ∈ M d 𝔏 β, ν {f | suppNum f = 1} = 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : PolymerEndpoint.Atomic.Cell d → Ω → ℝ) (hX : PolymerEndpoint.Atomic.IsEnvironment X 𝔏 P) :
    ∀ᵐ a ∂P, Tendsto (fun K : ℕ => liminf (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, centerMass X β i (K : ℝ) a) atTop) atTop (𝓝 1) := by sorry

end PolymerEndpoint.GeoLoc
