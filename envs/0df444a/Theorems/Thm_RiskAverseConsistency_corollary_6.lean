-- Prove2me | Theorems.Thm_RiskAverseConsistency_corollary_6
-- name    : RiskAverseConsistency.corollary_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:23:21.365668+00:00
-- url     : https://prove2.me/theorems/d727cde6-5191-4265-a8fb-62ba439a8820
-- title:
--   Corollary 6 — strong subsequential convergence for R-function regularizers
-- statement:
--   Let $Z$ be a reflexive Banach space, $Z_{\mathrm{ad}}\subset Z$ nonempty, closed and convex, $\wp:Z\to[0,\infty)$ convex and continuous, and $Z_0\subset Z$ bounded. Suppose $f_k:Z_{\mathrm{ad}}\to(-\infty,\infty]$ Mosco-epiconverges to $f:Z_{\mathrm{ad}}\to(-\infty,\infty]$, and let $(\varepsilon_k)\subset[0,\infty)$ with $\varepsilon_k\to0^+$. Define
--
--   $$
--   \mathfrak m_k^*=\inf_{z\in Z_{\mathrm{ad}}}\{f_k(z)+\wp(z)\},\qquad \mathfrak m^*=\inf_{z\in Z_{\mathrm{ad}}}\{f(z)+\wp(z)\},
--   $$
--
--   $$
--   \mathscr S_k^{\varepsilon_k}=\{z\in Z_{\mathrm{ad}}:f_k(z)+\wp(z)\le\mathfrak m_k^*+\varepsilon_k\},\qquad \mathscr S=\{z\in Z_{\mathrm{ad}}:f(z)+\wp(z)=\mathfrak m^*\}.
--   $$
--
--   Suppose $\mathscr S\ne\emptyset$ (with $\mathfrak m^*$ finite, the convention under which $\mathscr S$ is defined) and, for all $k$, $\mathscr S_k^{\varepsilon_k}\subset Z_0$ and $\mathscr S_k^{\varepsilon_k}\ne\emptyset$.
--
--   If, in addition, $\wp$ is an R-function and $z_k\in\mathscr S_k^{\varepsilon_k}$ for all $k$, then each subsequence of $(z_k)$ has a further subsequence converging strongly (in norm) to an element of $\mathscr S$.
--
--   Differences from the source:
--   - encoding: functions with values in (−∞, ∞] → EReal-valued functions with the value ⊥ = −∞ excluded on the domain set; reason: Lean convention; same instances
--   - encoding: functions defined on the subset (V₀, Z_ad, Y₀) → functions on the ambient space whose values off the subset are never used; reason: Lean convention; every quantifier is restricted to the subset, so no instance changes
--   - encoding: subsequence (v_k)_K, K ∋ k → ∞ → v ∘ K with K : ℕ → ℕ strictly increasing; reason: Lean convention; same subsequences
--   - encoding: 𝒮 is defined only when 𝔪* = inf (f + φ) is finite (convention of p.4) → hypothesis 𝔪* ≠ ⊤; reason: nondegeneracy condition excluding only the case in which 𝒮 is undefined; without it the printed conclusion fails (Z = ℓ², Z_ad = Z₀ the unit ball, f_k = f ≡ +∞, φ = ‖·‖², z_k = e_k)
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.7, Corollary 6

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_RiskAverseConsistency_MoscoConvergesOn
import Definitions.Def_RiskAverseConsistency_optimalValue
import Definitions.Def_RiskAverseConsistency_epsSolutionSet
import Definitions.Def_RiskAverseConsistency_solutionSet
import Definitions.Def_RiskAverseConsistency_IsRFunction

open Filter Topology QuasiHemiVI.Existence

namespace RiskAverseConsistency

/-- **Corollary 6.** If the hypotheses of Proposition 5 hold and `℘` is an R-function, then each
subsequence of `(zₖ)` has a further subsequence converging strongly (in norm) to an element of `𝒮`.

Milz, Surowiec, arXiv:2207.14756v2, Corollary 6, p.7.

Formalization Note: `(−∞, ∞]`-valued functions are `EReal`-valued with `⊥ = −∞` excluded on
`Z_ad`; `℘ : Z → [0, ∞)` is real with `0 ≤ ℘`. `𝔪*ₖ`, `𝔪*` are `optimalValue` (infima in `EReal`),
`𝒮^{εₖ}ₖ` is `epsSolutionSet` and `𝒮` is `solutionSet`. The hypothesis `𝔪* ≠ +∞` is the convention of
p.4 under which `𝒮` is defined ("provided that inf f is finite"); without it the statement is false
(`Z = ℓ²`, `Z_ad = Z₀` the closed unit ball, `fₖ = f ≡ +∞`, `℘ = ‖·‖²`, `zₖ = eₖ`). Subsequences are
compositions with strictly increasing maps. -/
theorem corollary_6 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (hZ : IsReflexive Z) {Zad : Set Z} (hZad_ne : Zad.Nonempty) (hZad_closed : IsClosed Zad)
    (hZad_convex : Convex ℝ Zad) (φ : Z → ℝ) (hφ_nonneg : ∀ z, 0 ≤ φ z)
    (hφ_convex : ConvexOn ℝ Set.univ φ) (hφ_cont : Continuous φ) {Z₀ : Set Z}
    (hZ₀ : Bornology.IsBounded Z₀) (f : ℕ → Z → EReal) (flim : Z → EReal)
    (hf_ne_bot : ∀ k, ∀ z ∈ Zad, f k z ≠ ⊥) (hflim_ne_bot : ∀ z ∈ Zad, flim z ≠ ⊥)
    (hMosco : MoscoConvergesOn Zad f flim) (ε : ℕ → ℝ) (hε_nonneg : ∀ k, 0 ≤ ε k)
    (hε : Tendsto ε atTop (𝓝 0))
    (hS_ne : (solutionSet Zad (fun z => flim z + (φ z : EReal))).Nonempty)
    (hm_ne_top : optimalValue Zad (fun z => flim z + (φ z : EReal)) ≠ ⊤)
    (hSk : ∀ k, epsSolutionSet Zad (fun z => f k z + (φ z : EReal)) (ε k) ⊆ Z₀ ∧
      (epsSolutionSet Zad (fun z => f k z + (φ z : EReal)) (ε k)).Nonempty)
    (z : ℕ → Z) (hz : ∀ k, z k ∈ epsSolutionSet Zad (fun z => f k z + (φ z : EReal)) (ε k))
    (hR : IsRFunction φ) (K : ℕ → ℕ) (hK : StrictMono K) :
    ∃ K₁ : ℕ → ℕ, StrictMono K₁ ∧
      ∃ zbar ∈ solutionSet Zad (fun z => flim z + (φ z : EReal)),
        Tendsto (fun j => z (K (K₁ j))) atTop (𝓝 zbar) := by sorry

end RiskAverseConsistency
