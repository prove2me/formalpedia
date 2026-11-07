-- Prove2me | Theorems.Thm_PolySphereLP_lemma_3_2_covariance
-- name    : PolySphereLP.lemma_3_2_covariance
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:24.058145+00:00
-- url     : https://prove2.me/theorems/fdea242d-932a-4f80-b95d-7e47f7e1116c
-- title:
--   Lemma 3.2 — data homogeneity and the top-block covariance
-- statement:
--   Assume $n\ge3$, $d\ge2$ even, $q\ge2d$ and $2d\mid q$; let $r=q/d$, $h=h_{n,d}$, $H=h_{n,q}$, fix an $L^2(\sigma)$-orthonormal basis of $\mathcal H_{n,d}$, and let $\nu=\mathrm{Unif}(S^{h-1})$.
--   1. For every fixed polynomial $g$, $Z_g(\mathbf a)=\int g(x)F_{\mathbf a}(x)\,d\sigma(x)$ is a homogeneous polynomial of degree $r$ in $\mathbf a$ (possibly zero).
--   2. For $x,y\in S^{n-1}$,
--   $$\mathbb E_{\mathbf a\sim\nu}\big[F_{\mathbf a}(x)F_{\mathbf a}(y)\big]=v_{n,d,r}\,Q^{(n)}_q(\langle x,y\rangle),\qquad v_{n,d,r}=r!\,\frac{h^r}{\mathrm R_{h,r}}\,\frac{\ell^r_{n,d}}{\ell_{n,q}}\le r!. \tag{44}$$
--   3. Consequently,
--   $$\mathbb E_{\mathbf a\sim\nu}\big[Z_g(\mathbf a)^2\big]=\frac{v_{n,d,r}}{H}\,\|\Pi_qg\|^2_{L^2(\sigma)}. \tag{45}$$
--
--   **Formalization Note** $Q^{(n)}_q$ is the published normalized Gegenbauer polynomial `SphereSOS.Rate.geg n q`. The basis is indexed by $\{0,\dots,h-1\}$ and $\nu$ is the uniform measure on $S^{h-1}$.
--
--   Differences from the source:
--   - generalization: Z_g a homogeneous polynomial of degree r in a ∈ S^{h−1} → Z_g(a) = Q(a) for all a ∈ ℝ^h with Q homogeneous of degree r; reason: P_a, F_a and Z_g are given by the same formulas for every a; restricting to the sphere gives the page's claim
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Lemma 3.2, p.17, eqs. (44)–(45)

import Mathlib
import Definitions.Def_SphereSOS_Rate_Sphere
import Definitions.Def_SphereSOS_Rate_SphereMeasure
import Definitions.Def_SphereSOS_Rate_Gegenbauer
import Definitions.Def_PolySphereLP_hdim
import Definitions.Def_PolySphereLP_IsHarmonicONB
import Definitions.Def_PolySphereLP_Zg
import Definitions.Def_PolySphereLP_vconst
open MvPolynomial MeasureTheory

namespace PolySphereLP

/-- **Lemma 3.2 (Data homogeneity and the top-block covariance).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Lemma 3.2, p.17,
eqs. (44)–(45).

With `r = q/d`, `h = h_{n,d}`, `H = h_{n,q}`, `F_a = Π_q(P_a^r)`, `ν = Unif(S^{h−1})`:
1. For every polynomial `g`, `Z_g(a) = ∫ g F_a dσ` is a homogeneous polynomial of degree `r` in `a`
   (possibly zero).
2. (44) `E_{a∼ν}[F_a(x)F_a(y)] = v_{n,d,r} Q_q^{(n)}(⟨x,y⟩)` for `x, y ∈ S^{n−1}`, and `v_{n,d,r} ≤ r!`.
3. (45) `E_{a∼ν}[Z_g(a)²] = (v_{n,d,r}/H) ‖Π_q g‖²_{L²(σ)}`.

**Formalization Note.** Standing assumptions of §2–3 (pp.9, 16): `n ≥ 3`, `d ≥ 2` even, `q ≥ 2d`,
`2d ∣ q`. The basis `Y` is any `L²(σ)`-orthonormal basis of `ℋ_{n,d}` (so `h = h_{n,d}`).
`Q_q^{(n)} = SphereSOS.Rate.geg n q`. Clause 1 is stated for all `a ∈ ℝ^h`. -/
theorem lemma_3_2_covariance (n d q : ℕ) (hn : 3 ≤ n) (hd : 2 ≤ d) (hde : Even d)
    (hq : 2 * d ≤ q) (hdq : 2 * d ∣ q) (h : ℕ) (Y : Fin h → MvPolynomial (Fin n) ℝ)
    (hY : IsHarmonicONB n d h Y) :
    (∀ g : MvPolynomial (Fin n) ℝ, ∃ Q : MvPolynomial (Fin h) ℝ, Q.IsHomogeneous (q / d) ∧
      ∀ a : Fin h → ℝ, Zg n q (q / d) Y g a = eval a Q) ∧
    (∀ x ∈ SphereSOS.Rate.sphere n, ∀ y ∈ SphereSOS.Rate.sphere n,
      ∫ a, eval x (Fa n q (q / d) Y a) * eval y (Fa n q (q / d) Y a) ∂(SphereSOS.Rate.sigma h) =
        vconst n d (q / d) * (SphereSOS.Rate.geg n q).eval (∑ i, x i * y i)) ∧
    vconst n d (q / d) ≤ ((q / d).factorial : ℝ) ∧
    (∀ g : MvPolynomial (Fin n) ℝ,
      ∫ a, Zg n q (q / d) Y g a ^ 2 ∂(SphereSOS.Rate.sigma h) =
        vconst n d (q / d) / (hdim n q : ℝ) *
          ∫ x, eval x (piProj n q g) ^ 2 ∂(SphereSOS.Rate.sigma n)) := by sorry

end PolySphereLP
