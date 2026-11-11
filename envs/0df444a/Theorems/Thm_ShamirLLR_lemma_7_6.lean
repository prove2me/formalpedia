-- Prove2me | Theorems.Thm_ShamirLLR_lemma_7_6
-- name    : ShamirLLR.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:01.781854+00:00
-- url     : https://prove2.me/theorems/3f8f984a-0108-41c5-9c11-0685313f741a
-- title:
--   Lemma 7.6 — summing the supported relations (weight bound $M$)
-- statement:
--   Let $p$ be an odd prime, $(a_i)_{i\in I}$ distinct nonzero places, $r'\ge1$, $\tilde L_i(x)=\sum_{h<r'}a_i^hx_h$, and for each $i$ let $\beta_{i,1},\beta_{i,2}\in\mathbb F_p^{d_i}$ and $E_i=\mathrm{span}\{\beta_{i,1},\beta_{i,2}\}$. Let $R$ be the space of tuples $\gamma\in\prod_iE_i^*$ whose polynomial $Q_\gamma$ vanishes identically. Let $0\le M\le1$ and let $\mu_i:E_i^*\to[0,\infty)$ satisfy $\mu_i(0)=1$, $\sum_\gamma\mu_i(\gamma)^2\le2$ and $\mu_i(\gamma)\le M$ for $\gamma\neq0$. Put $S_i=\mathrm{supp}\,\mu_i$, $V_0=\mathrm{span}(R\cap\prod_iS_i)$, $s_0=\dim V_0$. If $2s_0\le r'+1$, then
--   $$
--   \sum_{\gamma\in R,\ \gamma\neq0}\ \prod_{i\in I}\mu_i(\gamma_i)\le 2^{s_0}M^{r'+1-2s_0}.
--   $$
--
--   With $M=\sigma=2^{-1/2}$ this is the printed lemma; with $M=M_p$ it is the form used in Proposition 9.2.
--
--   Differences from the source:
--   - generalization: $\sigma=2^{-1/2}$ and the weights of Eq. (58) → any weights with $\mu_i\ge0$, $\mu_i(0)=1$, $\sum\mu_i^2\le2$, $\mu_i(\gamma)\le M$ for $\gamma\neq0$, and any $0\le M\le1$; reason: the proof uses only these properties; the weights of Eq. (58) satisfy them with $M=\sigma$ (Lemma 7.5), and Proposition 9.2 replaces $\sigma$ by $M_p$
--   - generalization: the §7.4 setting (blocks $I=J^c$ of a tuple in $\mathcal A_{p,m}$, $r'=r-|J|$, orbit coefficients $\beta_{i,1},\beta_{i,2}\in\mathbb F_p^{d_i}$ with $d_i\le D$) → any finite index set $I$ with distinct nonzero places, any $r'\ge1$, any $\beta_{i,1},\beta_{i,2}\in\mathbb F_p^{d_i}$ with no bound on $d_i$; reason: the proof uses only the Vandermonde property of distinct places and the weight properties; the §7.4 data are an instance
--   - encoding: $Q_\gamma$ identically zero as a polynomial → `relPoly … = 0` in `MvPolynomial (Fin r') (ZMod p)`; sums over $E_i^*$ with `Fintype` instances; reason: same objects
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Lemma 7.6, Eq. (61), p.56, setting of §7.4, pp.54–55 (PDF pp.57, 55–56); used with $M_p$ in the proof of Proposition 9.2, p.64

import Mathlib
import Definitions.Def_ShamirLLR_relations

set_option autoImplicit false

namespace ShamirLLR

open Classical in
/-- **Lemma 7.6 (Summing the supported relations), with a general weight bound `M`.** Let `p`
be an odd prime, `(a_i)_{i ∈ I}` distinct nonzero places, `r' ≥ 1`,
`L̃_i(x) = ∑_{h < r'} a_i^h x_h`, and for each `i` let `β_{i,1}, β_{i,2} ∈ 𝔽_p^{d_i}`,
`E_i = span{β_{i,1}, β_{i,2}}`. Let `R` be the space of `γ ∈ ∏_i E_i^*` with `Q_γ ≡ 0`. Let
`μ_i : E_i^* → [0, ∞)` with `μ_i(0) = 1`, `∑_γ μ_i(γ)² ≤ 2` and `μ_i(γ) ≤ M` for `γ ≠ 0`,
`0 ≤ M ≤ 1`. Put `S_i = supp μ_i`, `V₀ = span(R ∩ ∏_i S_i)`, `s₀ = dim V₀`. If `2s₀ ≤ r' + 1`,
then `∑_{γ ∈ R, γ ≠ 0} ∏_i μ_i(γ_i) ≤ 2^{s₀} M^{r'+1−2s₀}`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Lemma 7.6, Eq. (61), p.56, in the setting of §7.4, Eq. (53)–(60), pp.54–55; Proposition 9.2
uses it "with σ replaced by M_p", p.64.

**Formalization Note.** The source states it with `M = σ = 2^{−1/2}` and the weights of
Eq. (58) (which have `μ_i(0) = 1`, `Σ μ_i² ≤ 2`, Lemma 7.5); the proof uses only these
properties. The `Fintype` instances on `E_i^*` only let the sums be written. -/
theorem lemma_7_6 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {I : Type} [Fintype I] [DecidableEq I]
    (a : I → ZMod p) (ha0 : ∀ i, a i ≠ 0) (hainj : Function.Injective a) (r' : ℕ) (hr' : 1 ≤ r')
    (d : I → ℕ) (β₁ β₂ : (i : I) → Fin (d i) → ZMod p)
    [∀ i, Fintype (Module.Dual (ZMod p) (blockSpace (β₁ i) (β₂ i)))]
    (μ : (i : I) → Module.Dual (ZMod p) (blockSpace (β₁ i) (β₂ i)) → ℝ) (M : ℝ)
    (hM0 : 0 ≤ M) (hM1 : M ≤ 1) (hμ0 : ∀ i γ, 0 ≤ μ i γ) (hμzero : ∀ i, μ i 0 = 1)
    (hμsq : ∀ i, ∑ γ, μ i γ ^ 2 ≤ 2) (hμM : ∀ i γ, γ ≠ 0 → μ i γ ≤ M) :
    2 * Module.finrank (ZMod p) (Submodule.span (ZMod p)
        {γ : (i : I) → Module.Dual (ZMod p) (blockSpace (β₁ i) (β₂ i)) |
          IsRelation a r' β₁ β₂ γ ∧ ∀ i, μ i (γ i) ≠ 0}) ≤ r' + 1 →
      ∑ γ ∈ (Finset.univ : Finset ((i : I) → Module.Dual (ZMod p) (blockSpace (β₁ i) (β₂ i)))).filter
          (fun γ => IsRelation a r' β₁ β₂ γ ∧ γ ≠ 0), ∏ i, μ i (γ i) ≤
        (2 : ℝ) ^ Module.finrank (ZMod p) (Submodule.span (ZMod p)
            {γ : (i : I) → Module.Dual (ZMod p) (blockSpace (β₁ i) (β₂ i)) |
              IsRelation a r' β₁ β₂ γ ∧ ∀ i, μ i (γ i) ≠ 0}) *
          M ^ (r' + 1 - 2 * Module.finrank (ZMod p) (Submodule.span (ZMod p)
            {γ : (i : I) → Module.Dual (ZMod p) (blockSpace (β₁ i) (β₂ i)) |
              IsRelation a r' β₁ β₂ γ ∧ ∀ i, μ i (γ i) ≠ 0})) := by sorry

end ShamirLLR
