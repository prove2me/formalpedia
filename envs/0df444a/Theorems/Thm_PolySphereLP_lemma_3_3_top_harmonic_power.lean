-- Prove2me | Theorems.Thm_PolySphereLP_lemma_3_3_top_harmonic_power
-- name    : PolySphereLP.lemma_3_3_top_harmonic_power
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:11.525419+00:00
-- url     : https://prove2.me/theorems/33c6a449-2047-4a95-a9bf-f65685418e11
-- title:
--   Lemma 3.3 — deterministic size of the top harmonic power
-- statement:
--   Let $n\ge3$ and $d\ge2$ even. Let $P\in\mathcal H_{n,d}$ be real with $\|P\|_{L^2(\sigma)}=1$, and put $F=\Pi_{dr}(P^r)$. Write $m=\lfloor n/2\rfloor$ and $b_{m,d}=\binom{m+d-1}d$. For every integer $r\ge1$,
--   $$\|F\|^2_{L^2(\sigma)}\ge\frac{r!}{\mathrm R_{n,dr}}\Big(\frac{d!}{d^d}\Big)^r\Big(\frac{\mathrm R_{n,d}\,b_{m,d}}{h_{n,d}}\Big)^r. \tag{46}$$
--   In particular, if $d\le dr=q\le n$, then
--   $$\|F\|^2_{L^2(\sigma)}\ge r!\Big(\frac{d!}{18^d\,d^d}\Big)^r. \tag{47}$$
--
--   **Formalization Note** $n\ge3$ and $d\ge2$ even are the standing assumptions of Sections 2–3; $\Pi_{dr}$ is the $L^2(\sigma)$ projection.
--
--   Differences from the source:
--   - encoding: Π_{dr} → piProj n (d*r); reason: the L²(σ) projection of (39)
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Lemma 3.3, p.18, eqs. (46)–(47)

import Mathlib
import Definitions.Def_SphereSOS_Rate_SphereMeasure
import Definitions.Def_PolySphereLP_hdim
import Definitions.Def_PolySphereLP_Rmom
import Definitions.Def_PolySphereLP_piProj
open MvPolynomial MeasureTheory

namespace PolySphereLP

/-- **Lemma 3.3 (Deterministic size of the top harmonic power).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Lemma 3.3, p.18,
eqs. (46)–(47).

Let `P ∈ ℋ_{n,d}` be real with `‖P‖_{L²(σ)} = 1`, `F = Π_{dr}(P^r)`, `m = ⌊n/2⌋`,
`b_{m,d} = (m+d−1 choose d)`. For every integer `r ≥ 1`,
`‖F‖²_{L²(σ)} ≥ (r!/R_{n,dr}) (d!/d^d)^r (R_{n,d} b_{m,d}/h_{n,d})^r` (46); in particular, if
`d ≤ dr = q ≤ n`, then `‖F‖²_{L²(σ)} ≥ r! (d!/(18^d d^d))^r` (47).

**Formalization Note.** Standing assumptions of §2–3 (pp.9, 16): `n ≥ 3`, `d ≥ 2` even. `r ≥ 1`
arbitrary, as on the page. -/
theorem lemma_3_3_top_harmonic_power (n d : ℕ) (hn : 3 ≤ n) (hd : 2 ≤ d) (hde : Even d)
    (P : MvPolynomial (Fin n) ℝ) (hP : P ∈ harmonicSpace n d)
    (hP1 : ∫ x, eval x P ^ 2 ∂(SphereSOS.Rate.sigma n) = 1) (r : ℕ) (hr : 1 ≤ r) :
    (r.factorial : ℝ) / Rmom n (d * r) * ((d.factorial : ℝ) / (d : ℝ) ^ d) ^ r *
        (Rmom n d * ((n / 2 + d - 1).choose d : ℝ) / (hdim n d : ℝ)) ^ r ≤
      ∫ x, eval x (piProj n (d * r) (P ^ r)) ^ 2 ∂(SphereSOS.Rate.sigma n) ∧
    (d ≤ d * r → d * r ≤ n →
      (r.factorial : ℝ) * ((d.factorial : ℝ) / (18 ^ d * (d : ℝ) ^ d)) ^ r ≤
        ∫ x, eval x (piProj n (d * r) (P ^ r)) ^ 2 ∂(SphereSOS.Rate.sigma n)) := by sorry

end PolySphereLP
