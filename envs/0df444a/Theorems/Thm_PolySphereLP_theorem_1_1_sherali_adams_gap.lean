-- Prove2me | Theorems.Thm_PolySphereLP_theorem_1_1_sherali_adams_gap
-- name    : PolySphereLP.theorem_1_1_sherali_adams_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:02.355169+00:00
-- url     : https://prove2.me/theorems/0b43e230-ab46-4068-8c9a-f6df8b538030
-- title:
--   Theorem 1.1 — Sherali–Adams-type gaps for powered moment LPs on random harmonics
-- statement:
--   Fix an even integer $d\ge2$ and constants $C,B>0$. There is a constant $c_{d,C,B}>0$ with the following property. Let $n\ge2d$, let $q$ satisfy $2d\mid q$ and $2d\le q\le n$, and fix a family $\mathcal G\subseteq\mathbb R[x]_{\le q}$ of at most $n^{Cq}$ polynomials nonnegative on $S^{n-1}$, independently of $\mathbf a$. Then, with probability at least $1-n^{-B}-e^{-n}$ over the random harmonic polynomial $P_{\mathbf a}$,
--   $$\frac{\mathrm{PowLP}_{q,\mathcal G}(P_{\mathbf a})}{\|P_{\mathbf a}\|_\infty}\ge\frac{c_{d,C,B}}{\sqrt{q\log n}}\Big(\frac nq\Big)^{d/2-1/2}. \tag{3}$$
--
--   Here $P_{\mathbf a}=\sum_ia_iY_i$ for any $L^2(\sigma)$-orthonormal basis $Y_1,\dots,Y_h$ of $\mathcal H_{n,d}$ and $\mathbf a\sim\mathrm{Unif}(S^{h-1})$, and $\mathrm{PowLP}_{q,\mathcal G}(P)=(\sup_{\mathcal L\in\mathcal F_{q,\mathcal G}}\mathcal L(P^r))^{1/r}$ with $r=q/d$. The probability statement is for each prescribed family $\mathcal G$; it is not a simultaneous assertion over all families.
--
--   For fixed $q$ the gap is of order $n^{d/2-1/2}/\sqrt{\log n}$: every moment LP of size $n^{O(q)}$ built from data-independent valid inequalities, including Sherali–Adams-type product families, overestimates the maximum of a random harmonic polynomial on the sphere by this factor.
--
--   **Formalization Note** The constant is chosen before $n$, $q$, the family and the basis, and the family and the basis before the event. The family is a list $g_1,\dots,g_M$ with $M\le n^{Cq}$ ($M=0$ is allowed: the paper notes the redundant test $1\ge0$ can be added). The ratio is written as $\text{bound}\cdot\|P_{\mathbf a}\|_\infty\le\mathrm{PowLP}$, with PowLP in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: PowLP/‖P_a‖_∞ ≥ bound → bound · ‖P_a‖_∞ ≤ PowLP, PowLP in [0,∞]; reason: ‖P_a‖_∞ > 0 since ‖P_a‖_{L²(σ)} = 1, and PowLP may be +∞
--   - encoding: with probability at least 1 − n^{−B} − e^{−n} → a measurable event E with ν(E) ≥ 1 − n^{−B} − e^{−n} on which (3) holds for a ∈ S^{h−1}; reason: inner-measure form; PowLP is a supremum over uncountably many functionals, so measurability of the good set is not given
--   - encoding: a family 𝒢 of at most n^{Cq} polynomials → an indexed list g : Fin M → ℝ[x] with M ≤ n^{Cq}; reason: a set of N polynomials is a list of length N, and a list with repetitions defines the same region as its set of entries, which is no larger
--   - encoding: linear functionals on ℝ[x]_{≤q} → linear functionals on all of ℝ[x] constrained through degree ≤ q; reason: restriction and linear extension give the same supremum of ℒ(P_a^r)
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Theorem 1.1, p.5, eq. (3)

import Mathlib
import Definitions.Def_SphereSOS_Rate_Sphere
import Definitions.Def_SphereSOS_Rate_SphereMeasure
import Definitions.Def_PolySphereLP_IsHarmonicONB
import Definitions.Def_PolySphereLP_Pa
import Definitions.Def_PolySphereLP_supNorm
import Definitions.Def_PolySphereLP_powLP

namespace PolySphereLP

/-- **Theorem 1.1 (Main theorem: Sherali–Adams-type gaps).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Theorem 1.1, p.5, eq. (3).

Fix an even integer `d ≥ 2` and constants `C, B > 0`. There is `c_{d,C,B} > 0` such that: for
`n ≥ 2d`, `q` with `2d ∣ q` and `2d ≤ q ≤ n`, and a family `𝒢 ⊆ ℝ[x]_{≤q}` of at most `n^{Cq}`
polynomials nonnegative on `S^{n−1}`, fixed independently of `a`, with probability at least
`1 − n^{−B} − e^{−n}` over `P_a`,
`PowLP_{q,𝒢}(P_a)/‖P_a‖_∞ ≥ (c_{d,C,B}/√(q log n)) (n/q)^{d/2−1/2}`.

**Formalization Note.** `c` is chosen before `n`, `q`, the family and the basis; the family
(indexed `Fin M → ℝ[x]`, repetitions allowed, `M = 0` allowed) and the basis `Y` before the event.
The ratio is written as `bound · ‖P_a‖_∞ ≤ PowLP` (`‖P_a‖_∞ > 0`, and `PowLP ∈ [0,∞]` may be `+∞`);
`r = q/d`. "With probability at least" is the inner-measure form (a measurable event `E` with
`ν(E) ≥ 1 − n^{−B} − e^{−n}`). `log` is natural; `d/2 − 1/2` is a real exponent. -/
theorem theorem_1_1_sherali_adams_gap (d : ℕ) (hd : 2 ≤ d) (hde : Even d) (C B : ℝ)
    (hC : 0 < C) (hB : 0 < B) :
    ∃ c : ℝ, 0 < c ∧ ∀ n q : ℕ, 2 * d ≤ n → 2 * d ∣ q → 2 * d ≤ q → q ≤ n →
      ∀ (M : ℕ) (g : Fin M → MvPolynomial (Fin n) ℝ), (M : ℝ) ≤ (n : ℝ) ^ (C * q) →
      (∀ j, (g j).totalDegree ≤ q) →
      (∀ j, ∀ x ∈ SphereSOS.Rate.sphere n, 0 ≤ MvPolynomial.eval x (g j)) →
      ∀ (h : ℕ) (Y : Fin h → MvPolynomial (Fin n) ℝ), IsHarmonicONB n d h Y →
      ∃ E : Set (Fin h → ℝ), MeasurableSet E ∧
        ENNReal.ofReal (1 - (n : ℝ) ^ (-B) - Real.exp (-(n : ℝ))) ≤ SphereSOS.Rate.sigma h E ∧
        ∀ a ∈ E, a ∈ SphereSOS.Rate.sphere h →
          ENNReal.ofReal (c / Real.sqrt ((q : ℝ) * Real.log n) *
              ((n : ℝ) / q) ^ ((d : ℝ) / 2 - 1 / 2) * supNorm n (Pa Y a)) ≤
            powLP n q (q / d) g (Pa Y a) := by sorry

end PolySphereLP
