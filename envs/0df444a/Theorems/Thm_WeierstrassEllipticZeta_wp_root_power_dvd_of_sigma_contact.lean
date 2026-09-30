-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_wp_root_power_dvd_of_sigma_contact
-- name    : WeierstrassEllipticZeta.wp_root_power_dvd_of_sigma_contact
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T02:26:06.15368+00:00
-- url     : https://prove2.me/theorems/ec5748fd-24c4-4d4d-95fb-e113da76d06f
-- title:
--   Polynomial root multiplicities from analytic elliptic contact
-- statement:
--   Let $\Lambda$ be a complex period lattice, with canonical Weierstrass functions $\wp$ and $\zeta$. Let $\sigma$ be entire, normalized by $\sigma(0)=0$ and $\sigma'(0)=1$, satisfying $\sigma'=\zeta\sigma$ away from $\Lambda$. Assume the established sigma and zeta identities:
--
--   - $\sigma$ is nonzero away from $\Lambda$;
--   - $\zeta(z+\omega)=\zeta(z)+\eta(\omega)$ for $\omega\in\Lambda$ and $z\notin\Lambda$;
--   - $\sigma(z+v)\sigma(z-v)=(\wp(v)-\wp(z))\sigma(z)^2\sigma(v)^2$ for $z,v\notin\Lambda$.
--
--   For any polynomial $p\in\mathbb C[T]$, any $z\notin\Lambda$, and any integer $U\ge0$, suppose
--
--   $$\left.\frac{d^j}{dw^j}p(\wp(w))\right|_{w=z}=0\qquad(0\le j<2U+1).$$
--
--   Then
--
--   $$(T-\wp(z))^{U+1}\mid p(T).$$
--
--   The result includes ramified values of $\wp$ and the zero polynomial. It transfers analytic contact in the parameter $w$ to root multiplicity in the polynomial variable $T$.
--
--   **Formalization Note.** The normalization and differential equation are packaged by the existing `EllipticSigmaDifferentialData` record. Nonvanishing, addition, and quasi-periodicity are explicit hypotheses, all supplied by already proved mission theorems in the connecting sketch. The proof derives the bound two for the local multiplicity of $\wp$; that bound is not assumed.
-- source:
--   Derived analytic-to-algebraic reduction for https://prove2.me/theorems/3386877f-5ae4-4d39-a745-e949468c0cff. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. The new lemma is an independent deduction from the normalized entire sigma differential data, sigma addition, and zeta quasi-periodicity, not a quotation of the paper zero estimate. It proves the local multiplicity bound two for wp and transfers analytic contact to polynomial root divisibility. Primary Lean sources: Mathlib Analysis/Analytic/Order.lean (analyticOrderAt_comp, analyticOrderAt_mul), Algebra/Polynomial/Div.lean (root-multiplicity factorization), and Analysis/Normed/Module/Connected.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The remaining statement explicitly retains the quantitative construction of a polynomial with high contact; no geometric degree estimate is being claimed as proved.

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination

noncomputable section
open Filter
open scoped Topology
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.wp_root_power_dvd_of_sigma_contact
    (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0)
    (hzeta : ∀ ω z : ℂ, ω ∈ L.lattice → z ∉ L.lattice →
      weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω)
    (hadd : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice →
      S.sigma (z + v) * S.sigma (z - v) =
        (L.weierstrassP v - L.weierstrassP z) * S.sigma z ^ 2 * S.sigma v ^ 2)
    (p : Polynomial ℂ) (z : ℂ) (hz : z ∉ L.lattice) (U : ℕ)
    (hcontact : ∀ j < 2 * U + 1,
      iteratedDeriv j (fun w => p.eval (L.weierstrassP w)) z = 0) :
    (Polynomial.X - Polynomial.C (L.weierstrassP z)) ^ (U + 1) ∣ p := by sorry
