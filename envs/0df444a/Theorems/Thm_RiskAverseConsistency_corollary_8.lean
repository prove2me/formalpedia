-- Prove2me | Theorems.Thm_RiskAverseConsistency_corollary_8
-- name    : RiskAverseConsistency.corollary_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:23:24.552112+00:00
-- url     : https://prove2.me/theorems/acd2a67f-f1f3-4ace-aef7-04f48e7de673
-- title:
--   Corollary 8 — convergence of optimal values and of $\varepsilon_k$-solution sets
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
--   Then
--
--   $$
--   \mathfrak m_k^*\to\mathfrak m^*\qquad(k\to\infty).
--   $$
--
--   If furthermore $\wp$ is an R-function, then
--
--   $$
--   \mathbb D(\mathscr S_k^{\varepsilon_k},\mathscr S)\to0\qquad(k\to\infty),
--   $$
--
--   where $\mathbb D(\Gamma,\Psi)=\sup_{x\in\Gamma}\operatorname{dist}(x,\Psi)$ is the deviation.
--
--   Applied pathwise to the empirical approximation, this corollary turns almost sure Mosco-epiconvergence into consistency of optimal values and solution sets (proof of Theorem 11).
--
--   Differences from the source:
--   - encoding: functions with values in (−∞, ∞] → EReal-valued functions with the value ⊥ = −∞ excluded on the domain set; reason: Lean convention; same instances
--   - encoding: functions defined on the subset (V₀, Z_ad, Y₀) → functions on the ambient space whose values off the subset are never used; reason: Lean convention; every quantifier is restricted to the subset, so no instance changes
--   - encoding: 𝒮 is defined only when 𝔪* = inf (f + φ) is finite (convention of p.4) → hypothesis 𝔪* ≠ ⊤; reason: nondegeneracy condition excluding only the case in which 𝒮 is undefined; without it the printed conclusion fails (Z = ℓ², Z_ad = Z₀ the unit ball, f_k = f ≡ +∞, φ = ‖·‖², z_k = e_k)
--   - encoding: 𝔻(Γ, Ψ) = sup dist(x, Ψ) as a real number → the published CompositeSAA.excess, valued in [0, ∞] (ENNReal), converging to 0 there; reason: Lean convention; the deviation of nonempty sets inside a bounded set from a nonempty set is finite, and convergence to 0 is the same
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.7, Corollary 8

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_RiskAverseConsistency_MoscoConvergesOn
import Definitions.Def_RiskAverseConsistency_optimalValue
import Definitions.Def_RiskAverseConsistency_epsSolutionSet
import Definitions.Def_RiskAverseConsistency_solutionSet
import Definitions.Def_RiskAverseConsistency_IsRFunction
import Definitions.Def_CompositeSAA_excess

open Filter Topology QuasiHemiVI.Existence

namespace RiskAverseConsistency

/-- **Corollary 8.** If the hypotheses of Proposition 5 hold, then `𝔪*ₖ → 𝔪*` as `k → ∞`. If
furthermore `℘` is an R-function, then `𝔻(𝒮^{εₖ}ₖ, 𝒮) → 0` as `k → ∞`.

Milz, Surowiec, arXiv:2207.14756v2, Corollary 8, p.7.

Formalization Note: `(−∞, ∞]`-valued functions are `EReal`-valued with `⊥ = −∞` excluded on
`Z_ad`; `℘ : Z → [0, ∞)` is real with `0 ≤ ℘`. `𝔪*ₖ`, `𝔪*` are `optimalValue` (infima in `EReal`),
`𝒮^{εₖ}ₖ` is `epsSolutionSet` and `𝒮` is `solutionSet`. The hypothesis `𝔪* ≠ +∞` is the convention of
p.4 under which `𝒮` is defined ("provided that inf f is finite"); without it the statement is false
(`Z = ℓ²`, `Z_ad = Z₀` the closed unit ball, `fₖ = f ≡ +∞`, `℘ = ‖·‖²`, `zₖ = eₖ`). Subsequences are
compositions with strictly increasing maps. The deviation `𝔻` is computed in `[0, ∞]` (the published `CompositeSAA.excess`); the
optimal values converge in `EReal`. -/
theorem corollary_8 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
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
      (epsSolutionSet Zad (fun z => f k z + (φ z : EReal)) (ε k)).Nonempty) :
    Tendsto (fun k => optimalValue Zad (fun z => f k z + (φ z : EReal))) atTop
        (𝓝 (optimalValue Zad (fun z => flim z + (φ z : EReal)))) ∧
      (IsRFunction φ →
        Tendsto (fun k => CompositeSAA.excess (epsSolutionSet Zad (fun z => f k z + (φ z : EReal)) (ε k))
          (solutionSet Zad (fun z => flim z + (φ z : EReal)))) atTop (𝓝 0)) := by sorry

end RiskAverseConsistency
