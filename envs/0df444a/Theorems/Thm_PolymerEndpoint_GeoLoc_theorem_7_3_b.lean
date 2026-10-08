-- Prove2me | Theorems.Thm_PolymerEndpoint_GeoLoc_theorem_7_3_b
-- name    : PolymerEndpoint.GeoLoc.theorem_7_3_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:33:34.401166+00:00
-- url     : https://prove2.me/theorems/856a89a6-c949-494d-8363-2becfae14612
-- title:
--   Theorem 7.3(b), p. 49 — the single-copy condition (7.4) implies geometric localization with full density
-- statement:
--   Let $d\ge1$, $\mathfrak L$ non-degenerate with (1.1), $\beta>\beta_c$, and assume the **single-copy condition**
--   $$\nu(\{f\in\mathcal S:N(f)=1\})=1\quad\text{for all }\nu\in\mathcal M.\qquad(7.4)$$
--   Then the endpoint distributions $f_i=\rho_i(\omega_i=\cdot)$ are geometrically localized with full density: for every $\delta>0$ there is $K<\infty$ such that
--   $$\liminf_{n\to\infty}\frac1n\sum_{i=0}^{n-1}\mathbb 1_{\{f_i\in\mathcal G_{\delta,K}\}}\ge1-\delta\quad\text{a.s.}\qquad(1.11)$$
--
--   Whether (7.4) holds is open; the theorem shows it would upgrade the positive density of Theorem 1.2 to full density.
--
--   **Formalization Note.** $K$ is quantified for the given probability space, as in the printed definition (1.11); the theorem does not claim that $K$ is deterministic. $\beta>\beta_c$ is encoded as $\lim\mathbf E(F_n)<\lambda(\beta)$.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 49, Theorem 7.3(b), (7.4); p. 16, (1.11)

import Mathlib
import Definitions.Def_PolymerEndpoint_GeoLoc_Update
import Definitions.Def_PolymerEndpoint_GeoLoc_Functionals
open MeasureTheory ProbabilityTheory Filter Topology

namespace PolymerEndpoint.GeoLoc

open Classical in
/-- Theorem 7.3(b): if `β > β_c` and the single-copy condition (7.4) holds, the endpoint
distributions are geometrically localized with full density (1.11). -/
theorem theorem_7_3_b (d : ℕ) (hd : 1 ≤ d) (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (h𝔏 : ∀ c : ℝ, 𝔏 ≠ Measure.dirac c) (β : ℝ) (hβ : 0 ≤ β)
    (hmgf : ∀ α ∈ Set.Icc (-2 * β) (2 * β), Integrable (fun x => Real.exp (α * x)) 𝔏)
    (hlow : LowTemp d 𝔏 β)
    (hsingle : ∀ ν ∈ M d 𝔏 β, ν {f | suppNum f = 1} = 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : PolymerEndpoint.Atomic.Cell d → Ω → ℝ) (hX : PolymerEndpoint.Atomic.IsEnvironment X 𝔏 P) :
    ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, ∀ᵐ a ∂P,
      1 - δ ≤ liminf (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, if InG δ K (PolymerEndpoint.Atomic.endpt X β i a) then (1 : ℝ) else 0) atTop := by sorry

end PolymerEndpoint.GeoLoc
