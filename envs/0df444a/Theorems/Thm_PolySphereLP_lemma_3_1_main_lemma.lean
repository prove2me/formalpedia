-- Prove2me | Theorems.Thm_PolySphereLP_lemma_3_1_main_lemma
-- name    : PolySphereLP.lemma_3_1_main_lemma
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:34.510211+00:00
-- url     : https://prove2.me/theorems/6c2ed503-fefe-4928-b4de-6072453d3c9c
-- title:
--   Lemma 3.1 — finite-family powered-objective lower bound
-- statement:
--   Assume $n\ge3$, $d\ge2$ is even, $2d\mid q$ and $2d\le q\le n$; let $r=q/d$, $h=h_{n,d}$, $H=h_{n,q}$. Let $\mathcal G=\{g_1,\dots,g_M\}$, $M\ge1$, be a family of polynomials of degree at most $q$, nonnegative on the sphere, fixed independently of $\mathbf a$. For $0<\delta<1$ set
--   $$s=\max\{2,\log(M/\delta)\},\qquad \alpha_\star=\frac{\sqrt H}{2e\,3^q\sqrt{r!}\,(s-1)^{r/2}}. \tag{42}$$
--   With probability at least $1-\delta$ over $\mathbf a\sim\nu$, the functional $\mathcal L_{\mathbf a,\alpha_\star}$ of (39) belongs to $\mathcal F_{q,\mathcal G}$, and on the same event
--   $$\mathrm{PowLP}_{q,\mathcal G}(P_{\mathbf a})\ge c_d\Big(\frac nq\Big)^{d/2}\sqrt{\frac rs},\qquad c_d=\frac{d!}{54^d\,d^d\,e\sqrt2}. \tag{43}$$
--
--   **Formalization Note** "With probability at least $1-\delta$" means: there is a measurable event of $\nu$-probability at least $1-\delta$ on which both conclusions hold. The family and the basis are fixed before the event. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: with probability at least 1 − δ → a measurable event E with ν(E) ≥ 1 − δ on which the conclusions hold for a ∈ S^{h−1}; reason: inner-measure form; PowLP is a supremum over uncountably many functionals, so measurability of the good set is not given
--   - encoding: linear functionals on ℝ[x]_{≤q}; ℒ_{a,α} defined on ℝ[x]_{≤q} → linear functionals on all of ℝ[x] constrained through degree ≤ q; ℒ_{a,α} given by the same formula on ℝ[x]; reason: restriction and linear extension give the same values on degree ≤ q polynomials, so feasibility and the supremum are unchanged
--   - encoding: PowLP real-valued or +∞ → PowLP in [0,∞]; reason: the value may be +∞
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Lemma 3.1, pp.16–17, eqs. (42)–(43)

import Mathlib
import Definitions.Def_SphereSOS_Rate_Sphere
import Definitions.Def_SphereSOS_Rate_SphereMeasure
import Definitions.Def_PolySphereLP_hdim
import Definitions.Def_PolySphereLP_IsHarmonicONB
import Definitions.Def_PolySphereLP_powLP
import Definitions.Def_PolySphereLP_witness

namespace PolySphereLP

/-- **Lemma 3.1 (Finite-family powered-objective lower bound).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Lemma 3.1, pp.16–17,
eqs. (42)–(43).

Assume `n ≥ 3`, `d ≥ 2` even, `2d ∣ q`, `2d ≤ q ≤ n`, `r = q/d`, `H = h_{n,q}`. Let
`𝒢 = {g₁,…,g_M}`, `M ≥ 1`, be nonnegative polynomials on the sphere of degree `≤ q`, fixed
independently of `a`. For `0 < δ < 1` set `s = max{2, log(M/δ)}` and
`α★ = √H / (2e 3^q √(r!) (s−1)^{r/2})`. With probability at least `1 − δ` over `a ∼ ν`, the
functional `ℒ_{a,α★}` of (39) belongs to `ℱ_{q,𝒢}`, and on the same event
`PowLP_{q,𝒢}(P_a) ≥ c_d (n/q)^{d/2} √(r/s)`, `c_d = d!/(54^d d^d e √2)`.

**Formalization Note.** "With probability at least `1 − δ`" is the inner-measure form: a measurable
event `E` with `ν(E) ≥ 1 − δ` on which (for `a ∈ S^{h−1}`) both conclusions hold. The tests and the
basis `Y` are quantified before the event. `log` is natural, `e = exp 1`, real powers via `rpow`. -/
theorem lemma_3_1_main_lemma (n d q : ℕ) (hn : 3 ≤ n) (hd : 2 ≤ d) (hde : Even d)
    (hdq : 2 * d ∣ q) (hq : 2 * d ≤ q) (hqn : q ≤ n)
    (M : ℕ) (hM : 1 ≤ M) (g : Fin M → MvPolynomial (Fin n) ℝ)
    (hgdeg : ∀ j, (g j).totalDegree ≤ q)
    (hg : ∀ j, ∀ x ∈ SphereSOS.Rate.sphere n, 0 ≤ MvPolynomial.eval x (g j))
    (h : ℕ) (Y : Fin h → MvPolynomial (Fin n) ℝ) (hY : IsHarmonicONB n d h Y)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let r : ℕ := q / d
    let s : ℝ := max 2 (Real.log ((M : ℝ) / δ))
    let H : ℝ := (hdim n q : ℝ)
    let αstar : ℝ := Real.sqrt H /
      (2 * Real.exp 1 * 3 ^ q * Real.sqrt (r.factorial : ℝ) * (s - 1) ^ ((r : ℝ) / 2))
    let cd : ℝ := (d.factorial : ℝ) / (54 ^ d * (d : ℝ) ^ d * Real.exp 1 * Real.sqrt 2)
    ∃ E : Set (Fin h → ℝ), MeasurableSet E ∧
      ENNReal.ofReal (1 - δ) ≤ SphereSOS.Rate.sigma h E ∧
      ∀ a ∈ E, a ∈ SphereSOS.Rate.sphere h →
        witness n q r Y a αstar ∈ momentRegion n q g ∧
        ENNReal.ofReal (cd * ((n : ℝ) / q) ^ ((d : ℝ) / 2) * Real.sqrt ((r : ℝ) / s)) ≤
          powLP n q r g (Pa Y a) := by sorry

end PolySphereLP
