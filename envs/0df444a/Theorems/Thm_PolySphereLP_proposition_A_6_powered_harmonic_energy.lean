-- Prove2me | Theorems.Thm_PolySphereLP_proposition_A_6_powered_harmonic_energy
-- name    : PolySphereLP.proposition_A_6_powered_harmonic_energy
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:05.07874+00:00
-- url     : https://prove2.me/theorems/0fe5ce1c-cb78-483f-b194-d7b6e6b2418e
-- title:
--   Proposition A.6 — trace-free energy of a powered harmonic
-- statement:
--   Let $n\ge3$ and $d\ge2$ even. Let $P\in\mathcal H_{n,d}$ be real with $\|P\|_{L^2(\sigma)}=1$, let $r\ge1$, put $q=dr$ and $F=\Pi_q(P^r)$. Then, with $m=\lfloor n/2\rfloor$ and $b_{m,d}=\binom{m+d-1}d$,
--   $$\|F\|^2_{L^2(\sigma)}\ge\frac{r!}{\mathrm R_{n,q}}\Big(\frac{d!}{d^d}\Big)^r\Big(\frac{\mathrm R_{n,d}\,b_{m,d}}{h_{n,d}}\Big)^r. \tag{64}$$
--
--   The top harmonic component of a power of a normalized harmonic therefore carries substantial energy; this drives the objective lower bound of the main lemma.
--
--   **Formalization Note** $n\ge3$ and $d\ge2$ even are the standing assumptions of Section 2. $\Pi_q$ is the $L^2(\sigma)$ projection, and $\|F\|^2_{L^2(\sigma)}=\int F^2\,d\sigma$.
--
--   Differences from the source:
--   - encoding: Π_q → piProj n q (the L²(σ) projection onto ℋ_{n,q}); reason: on homogeneous input it coincides with the Fischer top component of (16)
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Proposition A.6, p.29, eq. (64)

import Mathlib
import Definitions.Def_SphereSOS_Rate_SphereMeasure
import Definitions.Def_PolySphereLP_hdim
import Definitions.Def_PolySphereLP_Rmom
import Definitions.Def_PolySphereLP_piProj
open MvPolynomial MeasureTheory

namespace PolySphereLP

/-- **Proposition A.6 (Trace-free energy of a powered harmonic).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Proposition A.6, p.29,
eq. (64).

Let `P ∈ ℋ_{n,d}` be real with `‖P‖_{L²(σ)} = 1`, `r ≥ 1`, `q = dr`, `F = Π_q(P^r)`. With `m = ⌊n/2⌋`
and `b_{m,d} = (m+d−1 choose d)`,
`‖F‖²_{L²(σ)} ≥ (r!/R_{n,q}) (d!/d^d)^r (R_{n,d} b_{m,d}/h_{n,d})^r`.

**Formalization Note.** Standing assumptions of §2 (p.9): `n ≥ 3`, `d ≥ 2` even (false at `d = 0`:
`P = 1`, `r = 2` gives `1 ≥ 2`). `r ≥ 1` arbitrary, as on the page. `Π_q` is the `L²(σ)` projection
`piProj`; `‖·‖²_{L²(σ)}` is `∫ (·)² dσ`. -/
theorem proposition_A_6_powered_harmonic_energy (n d : ℕ) (hn : 3 ≤ n) (hd : 2 ≤ d)
    (hde : Even d) (P : MvPolynomial (Fin n) ℝ) (hP : P ∈ harmonicSpace n d)
    (hP1 : ∫ x, eval x P ^ 2 ∂(SphereSOS.Rate.sigma n) = 1) (r : ℕ) (hr : 1 ≤ r) :
    (r.factorial : ℝ) / Rmom n (d * r) * ((d.factorial : ℝ) / (d : ℝ) ^ d) ^ r *
        (Rmom n d * ((n / 2 + d - 1).choose d : ℝ) / (hdim n d : ℝ)) ^ r ≤
      ∫ x, eval x (piProj n (d * r) (P ^ r)) ^ 2 ∂(SphereSOS.Rate.sigma n) := by sorry

end PolySphereLP
