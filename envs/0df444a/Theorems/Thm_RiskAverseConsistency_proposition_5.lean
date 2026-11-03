-- Prove2me | Theorems.Thm_RiskAverseConsistency_proposition_5
-- name    : RiskAverseConsistency.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:23:15.097951+00:00
-- url     : https://prove2.me/theorems/b9a40bc3-15a8-4ef7-aa4e-a45acbb28107
-- title:
--   Proposition 5 — weak compactness of approximate minimizers of regularized problems
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
--   If $z_k\in\mathscr S_k^{\varepsilon_k}$ for all $k$ and $(z_k)_K$ is a subsequence, then $(z_k)_K$ has a further subsequence $(z_k)_{K_1}$ converging weakly to some $\bar z\in\mathscr S$ with $\wp(z_k)\to\wp(\bar z)$ as $K_1\ni k\to\infty$.
--
--   The regularizer converges along the subsequence even though only weak convergence of $(z_k)$ is available; this is what Corollaries 6 and 8 upgrade to strong convergence and to convergence of solution sets.
--
--   Differences from the source:
--   - encoding: functions with values in (−∞, ∞] → EReal-valued functions with the value ⊥ = −∞ excluded on the domain set; reason: Lean convention; same instances
--   - encoding: functions defined on the subset (V₀, Z_ad, Y₀) → functions on the ambient space whose values off the subset are never used; reason: Lean convention; every quantifier is restricted to the subset, so no instance changes
--   - encoding: subsequence (v_k)_K, K ∋ k → ∞ → v ∘ K with K : ℕ → ℕ strictly increasing; reason: Lean convention; same subsequences
--   - encoding: 𝒮 is defined only when 𝔪* = inf (f + φ) is finite (convention of p.4) → hypothesis 𝔪* ≠ ⊤; reason: nondegeneracy condition excluding only the case in which 𝒮 is undefined; without it the printed conclusion fails (Z = ℓ², Z_ad = Z₀ the unit ball, f_k = f ≡ +∞, φ = ‖·‖², z_k = e_k)
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.6, Proposition 5 (with (5) and the solution sets on p.6, and the convention of p.4)

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_RiskAverseConsistency_MoscoConvergesOn
import Definitions.Def_RiskAverseConsistency_optimalValue
import Definitions.Def_RiskAverseConsistency_epsSolutionSet
import Definitions.Def_RiskAverseConsistency_solutionSet

open Filter Topology QuasiHemiVI.Existence

namespace RiskAverseConsistency

/-- **Proposition 5.** Let `Z` be a reflexive Banach space, `Z_ad ⊂ Z` nonempty, closed and convex,
`℘ : Z → [0, ∞)` convex and continuous, and `Z₀ ⊂ Z` bounded. Suppose `fₖ : Z_ad → (−∞, ∞]`
Mosco-epiconverges to `f : Z_ad → (−∞, ∞]`, `(εₖ) ⊂ [0, ∞)`, `εₖ → 0⁺`, `𝒮 ≠ ∅`, and for all `k`,
`𝒮^{εₖ}ₖ ⊂ Z₀` and `𝒮^{εₖ}ₖ ≠ ∅`. If `zₖ ∈ 𝒮^{εₖ}ₖ` for all `k` and `(zₖ)_K` is a subsequence, then
`(zₖ)_K` has a further subsequence `(zₖ)_{K₁}` converging weakly to some `z̄ ∈ 𝒮` with
`℘(zₖ) → ℘(z̄)` as `K₁ ∋ k → ∞`. Here `𝔪*ₖ = inf_{Z_ad} (fₖ + ℘)`, `𝔪* = inf_{Z_ad} (f + ℘)`,
`𝒮^{εₖ}ₖ = {z ∈ Z_ad : fₖ(z) + ℘(z) ≤ 𝔪*ₖ + εₖ}`, `𝒮 = {z ∈ Z_ad : f(z) + ℘(z) = 𝔪*}` ((5), p.6).

Milz, Surowiec, arXiv:2207.14756v2, Proposition 5, p.6.

Formalization Note: `(−∞, ∞]`-valued functions are `EReal`-valued with `⊥ = −∞` excluded on
`Z_ad`; `℘ : Z → [0, ∞)` is real with `0 ≤ ℘`. `𝔪*ₖ`, `𝔪*` are `optimalValue` (infima in `EReal`),
`𝒮^{εₖ}ₖ` is `epsSolutionSet` and `𝒮` is `solutionSet`. The hypothesis `𝔪* ≠ +∞` is the convention of
p.4 under which `𝒮` is defined ("provided that inf f is finite"); without it the statement is false
(`Z = ℓ²`, `Z_ad = Z₀` the closed unit ball, `fₖ = f ≡ +∞`, `℘ = ‖·‖²`, `zₖ = eₖ`). Subsequences are
compositions with strictly increasing maps. -/
theorem proposition_5 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
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
    (K : ℕ → ℕ) (hK : StrictMono K) :
    ∃ K₁ : ℕ → ℕ, StrictMono K₁ ∧
      ∃ zbar ∈ solutionSet Zad (fun z => flim z + (φ z : EReal)),
        WeakConv (fun j => z (K (K₁ j))) zbar ∧
        Tendsto (fun j => φ (z (K (K₁ j)))) atTop (𝓝 (φ zbar)) := by sorry

end RiskAverseConsistency
