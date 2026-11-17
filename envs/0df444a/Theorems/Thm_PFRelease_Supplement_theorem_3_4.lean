-- Prove2me | Theorems.Thm_PFRelease_Supplement_theorem_3_4
-- name    : PFRelease.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:44:53.094061+00:00
-- url     : https://prove2.me/theorems/9ae480b0-30df-4b56-afdd-8141289978dd
-- title:
--   Theorem 3.4 — the element–block filter is $(\varepsilon,\delta)$-JDP with $\sigma=8/\varepsilon$, $\sigma'=(8/\varepsilon)\sqrt{\lceil24\ln(16/\delta)/\varepsilon\rceil\ln(4/\delta)}$
-- statement:
--   Let $n,b\in\mathbb N$ with $b>0$ dividing $n$, let $\varepsilon\in(0,1]$, $\delta\in(0,1)$, $t\ge0$, and let $F$ be a friendliness predicate. Set
--   $$
--   \sigma:=\frac8\varepsilon,\qquad \sigma':=\frac8\varepsilon\sqrt{\Big\lceil\frac{24\ln(16/\delta)}{\varepsilon}\Big\rceil\ln(4/\delta)},\qquad \kappa:=2\sigma\ln(16/\delta).
--   $$
--   Then the private filter $\mathcal F_{b,t,\kappa,\sigma,\sigma'}(F;\cdot)$ of Algorithm 1 (uniform random partition into blocks of size $b$, cap noise $\mathrm{Lap}(\sigma)$, test noises $\mathrm{Lap}(\sigma')$) is $(\varepsilon,\delta)$-jointly differentially private on datasets of $n$ records: for every $s\in\mathcal X^n$ and every slot $i$,
--   $$
--   \mathcal F(s)^{i\to\perp}\approx_{\varepsilon,\delta}\mathcal F(s^{i\to\perp}).
--   $$
--
--   The noise scales do not depend on $n$. Composed with a differentially private mechanism, such a filter gives a differentially private mechanism, and it is the privacy half of the analysis of PFR.
--
--   **Formalization Note** The filter's law is the published `filterLaw` and joint differential privacy is the published `IsJDP`, which compares the laws of the filtered datasets on every set of datasets. The ceiling is `Int.ceil` of a real number.
--
--   Differences from the source:
--   - encoding: n, b ∈ ℕ under the standing assumption that b divides n (§3.1, p.8) → hypotheses 0 < b and b ∣ n; reason: the paper assumes throughout that b divides n, and blocks of size b need b > 0
--   - encoding: the filter F_{b,t,κ,σ,σ′}(F; ·) and (ε, δ)-JDP on datasets of n records → IsJDP (filterLaw (n := n) b t κ σ σ′ F) ε δ; reason: the published base encodings of Algorithm 1 and Definition 3.3, the same objects
--   - encoding: ⌈24 ln(16/δ)/ε⌉ → Int.ceil of the real number, cast to ℝ; reason: Lean convention, same value
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem 3.4, p.10 (PDF p.12); restated as Theorem B.5, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_PFRelease_IsJDP
import Definitions.Def_PFRelease_filterLaw

open MeasureTheory

namespace PFRelease.Supplement

/-- **Theorem 3.4 (Privacy of the filter)** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private
Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem 3.4, p.10 = PDF p.12; restated as
Theorem B.5, p.32). Given `n, b ∈ ℕ`, `ε ∈ (0, 1]`, `δ ∈ (0, 1)`, `t ≥ 0` and a friendliness predicate
`F`, the filter `F_{b,t,κ,σ,σ′}(F; ·)` (Algorithm 1) on datasets of `n` records is `(ε, δ)`-JDP, where
`κ := 2σ ln(16/δ)`, `σ := 8/ε` and `σ′ := (8/ε)√(⌈24 ln(16/δ)/ε⌉ ln(4/δ))`.

**Formalization Note** The filter's law is the published `filterLaw` (uniform random equipartition,
independent Laplace noises); JDP is the published `IsJDP` (laws of filtered datasets compared on
every set of datasets). `b > 0` and `b ∣ n` are the paper's standing assumption that `b` divides `n`
(§3.1, p.8). The ceiling is `Int.ceil` of a real number, cast back to `ℝ`; the square root covers the
product `⌈24 ln(16/δ)/ε⌉ · ln(4/δ)`. -/
theorem theorem_3_4 {X : Type*} (n b : ℕ) (hb : 0 < b) (hbn : b ∣ n) (ε δ t : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ht : 0 ≤ t)
    (F : List (Option X) → Option X → Bool) :
    let σ := 8 / ε
    let σ' := (8 / ε) * Real.sqrt ((⌈24 * Real.log (16 / δ) / ε⌉ : ℝ) * Real.log (4 / δ))
    let κ := 2 * σ * Real.log (16 / δ)
    IsJDP (filterLaw (n := n) b t κ σ σ' F) ε δ := by sorry

end PFRelease.Supplement
