-- Prove2me | Theorems.Thm_PFRelease_Supplement_theorem_D_2
-- name    : PFRelease.Supplement.theorem_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:46:21.481616+00:00
-- url     : https://prove2.me/theorems/6cd67013-4944-4276-9e5b-ab6cb9ae03e5
-- title:
--   Theorem D.2 — scalar PFR $\mathrm{PFR}_b^{\varepsilon,\delta}(\mathcal N_{\sigma/(\tau n)}(g),\varphi,\tau)$ is $(\varepsilon,\delta)$-DP
-- statement:
--   Let $n,b\in\mathbb N$ with $n/b\in\mathbb N$, $\varepsilon\in(0,1]$, $\delta\in(0,1)$, and $\sigma>0$ with $\delta_{\mathcal N_\sigma}(\varepsilon/2)\le\delta/4$. Let $\tau>0$ be a friendliness threshold, $g$ a real-valued function on nonempty datasets, and $\Delta$ a function that bounds the per-instance sensitivity of $g$. Suppose the score
--   $$
--   \varphi(s,x):=\frac1{|s|\,\Delta(s,x)}\qquad(s\neq\emptyset,\ x\neq\perp,\ 1/0:=\infty,\ 1/\infty:=0)
--   $$
--   is a concave friendliness score, and
--   $$
--   n\ge\frac{400\,b\ln^2(16/\delta)}{\varepsilon^{3/2}}.
--   $$
--   Then $\mathrm{PFR}_b^{\varepsilon,\delta}\big(\mathcal N_{\sigma/(\tau n)}(g),\varphi,\tau\big)$ is $(\varepsilon,\delta)$-differentially private on datasets of $n$ records.
--
--   Here $\mathrm{PFR}_b^{\varepsilon,\delta}(M,\varphi,\tau)=M\circ\mathcal F_{b,t,\kappa,\sigma_F,\sigma_F'}(F_{2\tau}(\varphi))$ uses the parameters of Theorem 4.5: $L=\ln(16/\delta)$, $t=7n/(8b)$, $\sigma_F=12/\varepsilon$, $\sigma_F'=108L/\varepsilon^{3/2}$, $\kappa=2\sigma_FL$; and $\mathcal N_{\sigma/(\tau n)}(g)$ adds Gaussian noise of standard deviation $\sigma/(\tau n)$ to $g$.
--
--   The theorem turns a per-instance sensitivity bound with a concave reciprocal into a differentially private scalar release whose noise scales with the typical, not the worst-case, sensitivity.
--
--   **Formalization Note** The score is any function $\mathcal X^*\times\mathcal X\to[0,\infty]$ equal to $(|s|\,\Delta(s,x))^{-1}$ (inverse in $[0,\infty]$) on nonempty $s$ and non-null $x$; "concave friendliness score" is the published `IsScore` and `IsConcave`, and the first forces the value $0$ on the empty dataset. The PFR law is the published `compose` of the Gaussian mechanism over `filterLaw`; differential privacy is the published `IsDPOn`.
--
--   Differences from the source:
--   - encoding: n/b ∈ ℕ → hypotheses 0 < b and b ∣ n; reason: same instances
--   - encoding: PFR^{ε,δ}_b(N_{σ/(τn)}(g), φ, τ) → compose (gaussMech g (σ/(τn))) (filterLaw b t κ σ_F σ_F′ (predOf φ (2τ))) with t, κ, σ_F, σ_F′ of Theorem 4.5; reason: the definition of PFR^{ε,δ}_b on p.13 in the published base encodings
--   - encoding: the score φ defined for nonempty s and x ≠ ⊥ → any φ : X* × X → [0, ∞] equal to (|s| Δ(s, x))⁻¹ there, with IsScore φ and IsConcave φ; reason: the paper leaves φ(∅, x) to Definition 4.4 (which forces 0, as IsScore does) and the value at ⊥ free (footnote 5)
--   - encoding: Δ bounds the per-instance sensitivity of g, a real-valued function on nonempty datasets → IsPerInstanceBound g Δ with g : List (Option X) → ℝ; reason: Definition D.1 with its quantifier over every n ≥ 1; the value of g on the empty list is never used
--   - encoding: N_{σ/(τn)}(g) adds N(0, (σ/(τn))²) → gaussianReal (g s) ((σ/(τn))²); reason: Mathlib's Gaussian takes the variance
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem D.2, p.39 (PDF p.41); PFR^{ε,δ}_b, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_PFRelease_Indist
import Definitions.Def_PFRelease_compose
import Definitions.Def_PFRelease_IsScore
import Definitions.Def_PFRelease_IsConcave
import Definitions.Def_PFRelease_filterLaw
import Definitions.Def_PFRelease_Supplement_gaussMech

open MeasureTheory

namespace PFRelease.Supplement

/-- **Theorem D.2 (Scalar PFR)** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private
Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem D.2, p.39 = PDF p.41). Given `n, b ∈ ℕ` with
`n/b ∈ ℕ`, `ε ∈ (0, 1]`, `δ ∈ (0, 1)`, `σ > 0` with `δ_{N_σ}(ε/2) ≤ δ/4`, a friendliness threshold
`τ > 0`, a real-valued function `g` on nonempty datasets and a function `Δ` that bounds its per-instance
sensitivity, if the score `φ(s, x) := 1/(|s| Δ(s, x))` (nonempty `s`, `x ≠ ⊥`, `1/0 := ∞`, `1/∞ := 0`) is
a concave friendliness score and `n ≥ 400b ln²(16/δ)/ε^{3/2}`, then `PFR_b^{ε,δ}(N_{σ/(τn)}(g), φ, τ)` is
`(ε, δ)`-DP on datasets of `n` records.

**Formalization Note** `PFR_b^{ε,δ}(M, φ, τ) = M ∘ F_{b,t,κ,σ_F,σ_F′}(F_{2τ}(φ))` with the parameters of
Theorem 4.5 (p.13): `t = 7n/(8b)`, `σ_F = 12/ε`, `σ_F′ = 108L/ε^{3/2}`, `κ = 2σ_F L`, `L = ln(16/δ)`;
its law is the published `compose` over `filterLaw`. `N_{σ/(τn)}(g)` adds Gaussian noise of standard
deviation `σ/(τn)` (variance `(σ/(τn))²`). `φ` is any function `X* × X → [0, ∞]` equal to
`(|s| Δ(s, x))⁻¹` (in `ℝ≥0∞`) on nonempty `s` and `x ≠ ⊥`; its value on `∅` is forced to `0` by
`IsScore` and its value at `⊥` is free, as the paper leaves them. "Concave friendliness score" is
`IsScore φ ∧ IsConcave φ`. `b > 0`, `b ∣ n` encode `n/b ∈ ℕ`. -/
theorem theorem_D_2 {X : Type*} (n b : ℕ) (hb : 0 < b) (hbn : b ∣ n) (ε δ σ τ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ : 0 < σ)
    (hprof : gaussProfile σ (ε / 2) ≤ δ / 4) (hτ : 0 < τ)
    (g : List (Option X) → ℝ) (Δ : List (Option X) → Option X → ENNReal)
    (hΔ : IsPerInstanceBound g Δ) (φ : List (Option X) → Option X → ENNReal)
    (hφ : ∀ (l : List (Option X)) (x : Option X), l ≠ [] → x ≠ none →
      φ l x = ((l.length : ENNReal) * Δ l x)⁻¹)
    (hscore : IsScore φ) (hconc : IsConcave φ)
    (hn : 400 * (b : ℝ) * Real.log (16 / δ) ^ 2 / ε ^ (3 / 2 : ℝ) ≤ n) :
    let L := Real.log (16 / δ)
    let t := 7 * (n : ℝ) / (8 * (b : ℝ))
    let σF := 12 / ε
    let σF' := 108 * L / ε ^ (3 / 2 : ℝ)
    let κ := 2 * σF * L
    IsDPOn (compose (gaussMech (n := n) g (σ / (τ * n)))
      (filterLaw b t κ σF σF' (predOf φ (2 * τ)))) ε δ := by sorry

end PFRelease.Supplement
