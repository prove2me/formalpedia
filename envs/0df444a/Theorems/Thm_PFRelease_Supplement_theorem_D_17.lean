-- Prove2me | Theorems.Thm_PFRelease_Supplement_theorem_D_17
-- name    : PFRelease.Supplement.theorem_D_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:47:46.818385+00:00
-- url     : https://prove2.me/theorems/717274ac-5dd5-40de-9b5e-6c20084e52cc
-- title:
--   Theorem D.17 — the private KL divergence retains every record and has error $\le2\ln(2/\beta)/(\tau n\varepsilon)$
-- statement:
--   Fix public integers $T\ge1$ and $d\ge2$, and let records be histograms $H\in\mathbb Z_{\ge0}^d$ with $\sum_jH_j=T$. Let $n,b\in\mathbb N$ with $n/b\in\mathbb N$; $\varepsilon\in(0,1]$; $\delta\in(0,1)$; $\beta\in(0,1)$ with $\delta\le2\beta$; a public pseudocount $\lambda>0$; a friendliness threshold $\tau\in(0,1/4]$; and an input $s\in\mathcal X^n$ without null records whose histograms $H_i:=s_i$ satisfy condition (8):
--   $$
--   H_{ij}\le\frac{\lambda+\bar H_j(s)}{4\tau}\qquad\text{for all }i\in[n],\ j\in[d].
--   $$
--   If
--   $$
--   b\ge\frac4\tau\ln\frac{4nd}\beta\qquad\text{and}\qquad\frac nb\ge\max\Big\{\frac{400L^2}{\varepsilon^{3/2}},\ \frac{1800L\ln(8n/\beta)}{\varepsilon^{3/2}}\Big\},\qquad L:=\ln(16/\delta),
--   $$
--   then with probability at least $1-\beta$ the filter of $\mathrm{PFR}_b^{\varepsilon,\delta}(M_{\mathrm{KL}},\varphi_{\mathrm{KL}},\tau)$ retains every record, and its output $Y$ satisfies
--   $$
--   |Y-g_{\mathrm{KL}}(s)|\le\frac{2\ln(2/\beta)}{\tau n\varepsilon}.
--   $$
--
--   The filter is that of Theorem 4.5 ($t=7n/(8b)$, $\sigma_F=12/\varepsilon$, $\sigma_F'=108L/\varepsilon^{3/2}$, $\kappa=2\sigma_FL$) testing $F_{2\tau}(\varphi_{\mathrm{KL}})$. Under the deterministic condition (8), no user is extreme relative to the regularized average counts, and the error is of order $1/(\tau n\varepsilon)$ instead of the worst-case $T/(dn\lambda\varepsilon)$.
--
--   **Formalization Note** Histograms are `Fin d → ℕ` summing to $T$. Because the input has no null records, "retains every record" means the filter nulls the empty set, on which the output is $M_{\mathrm{KL}}(s)$; the probability of the joint event is the probability that the filter nulls nothing times $M_{\mathrm{KL}}(s)$ of the error event.
--
--   Differences from the source:
--   - encoding: T ≥ 1 and d ≥ 2, the standing assumptions of App. D.3 (p.47) → hypotheses 1 ≤ T and 2 ≤ d; reason: the setting of the theorem
--   - encoding: records H ∈ ℤ^d_{≥0} with Σ_j H_j = T, and ⊥ → Option (Histogram d T), Histogram d T = {H : Fin d → ℕ // Σ_j H j = T}; reason: same records
--   - encoding: with probability at least 1 − β, the filter retains every record and |Y − g_KL(s)| ≤ 2 ln(2/β)/(τnε) → filterLaw … s ∅ · M_KL(s){y : |y − g_KL(s)| ≤ 2 ln(2/β)/(τnε)} ≥ 1 − β; reason: with no null records, retaining every record is I = ∅, on which the PFR output is M_KL(s); this is the probability of the joint event
--   - encoding: PFR^{ε,δ}_b → the filter of Theorem 4.5 with t, κ, σ_F, σ_F′ of p.13 testing predOf φ_KL (2τ); reason: the definition of PFR^{ε,δ}_b on p.13
--   - encoding: n/b ∈ ℕ → hypotheses 0 < b and b ∣ n; reason: same instances
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem D.17 and condition (8), p.48 (PDF p.50); App. D.3, p.47 (PDF p.49); eq. (3), p.19 (PDF p.21)

import Mathlib
import Definitions.Def_PFRelease_IsScore
import Definitions.Def_PFRelease_filterLaw
import Definitions.Def_PFRelease_Supplement_klMech

open MeasureTheory

namespace PFRelease.Supplement

/-- **Theorem D.17 (Utility of the private KL divergence)** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private
Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem D.17, p.48 =
PDF p.50). Given `n, b ∈ ℕ` with `n/b ∈ ℕ`; `ε ∈ (0, 1]`; `δ ∈ (0, 1)`; `β ∈ (0, 1)` with `δ ≤ 2β`; a
public pseudocount `λ > 0`, a friendliness threshold `τ ∈ (0, 1/4]`, and an input `s ∈ Xⁿ` without null
records that satisfies (8), `H_{ij} ≤ (λ + H̄_j(s))/(4τ)` for all `i ∈ [n]`, `j ∈ [d]`, if
`b ≥ (4/τ) ln(4nd/β)` and `n/b ≥ max{400L²/ε^{3/2}, 1800L ln(8n/β)/ε^{3/2}}`, then with probability at
least `1 − β`, the filter of `PFR_b^{ε,δ}(M_KL, φ_KL, τ)` retains every record, and its output `Y`
satisfies `|Y − g_KL(s)| ≤ 2 ln(2/β)/(τnε)`, where `d` is the number of categories and `L := ln(16/δ)`.

**Formalization Note** Records are histograms `H ∈ ℕ^d` with `Σ_j H_j = T`; `d ≥ 2` and `T ≥ 1` are the
standing assumptions of App. D.3 (p.47). The filter is that of Theorem 4.5 (`t = 7n/(8b)`,
`σ_F = 12/ε`, `σ_F′ = 108L/ε^{3/2}`, `κ = 2σ_F L`) testing `F_{2τ}(φ_KL)`. The input has no null records,
so "retains every record" is the nulled set `I = ∅`, on which the output is `M_KL(s)`; the joint
probability of "`I = ∅` and `|Y − g_KL(s)| ≤ 2 ln(2/β)/(τnε)`" is `filterLaw … s ∅ · M_KL(s){…}`.
`b > 0`, `b ∣ n` encode `n/b ∈ ℕ`. -/
theorem theorem_D_17 {d T : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T) (n b : ℕ) (hb : 0 < b) (hbn : b ∣ n)
    (ε δ β lam τ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hδβ : δ ≤ 2 * β) (hlam : 0 < lam) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 4)
    (s : Fin n → Option (Histogram d T)) (hs : ∀ i, s i ≠ none)
    (h8 : ∀ (i : Fin n) (H : Histogram d T), s i = some H →
      ∀ j : Fin d, (H.1 j : ℝ) ≤ (lam + avgCount (toList s) j) / (4 * τ))
    (hblock : 4 / τ * Real.log (4 * n * d / β) ≤ b)
    (hm : max (400 * Real.log (16 / δ) ^ 2 / ε ^ (3 / 2 : ℝ))
        (1800 * Real.log (16 / δ) * Real.log (8 * n / β) / ε ^ (3 / 2 : ℝ)) ≤ (n : ℝ) / b) :
    let L := Real.log (16 / δ)
    let t := 7 * (n : ℝ) / (8 * (b : ℝ))
    let σF := 12 / ε
    let σF' := 108 * L / ε ^ (3 / 2 : ℝ)
    let κ := 2 * σF * L
    ENNReal.ofReal (1 - β) ≤
      filterLaw b t κ σF σF' (predOf (phiKL lam) (2 * τ)) s ∅ *
        mKL lam τ ε s {y | |y - gKL lam (toList s)| ≤ 2 * Real.log (2 / β) / (τ * n * ε)} := by sorry

end PFRelease.Supplement
