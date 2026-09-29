-- Prove2me | Theorems.Thm_Weinberg1965_photon_log_cutoff
-- name    : Weinberg1965.photon_log_cutoff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:53:43.400641+00:00
-- url     : https://prove2.me/theorems/edc66d05-5b7d-4275-ac49-bf7cd17a033a
-- title:
--   Eq. (2.13) — logarithmic cutoff dependence $-A\ln(\Lambda/\lambda)$
-- statement:
--   Let the external lines $n$ of a process have masses $m_n>0$, three-momenta $\mathbf p_n\in\mathbb R^3$, charges $e_n$ and signs $\eta_n=\pm1$, and let $A$ be the infrared-photon exponent of Eq. (2.14). For a null four-vector $q=(\mathbf q,|\mathbf q|)$ write $p_n\cdot q=\mathbf p_n\cdot\mathbf q-E_n|\mathbf q|$. Then for all cutoffs $0<\lambda<\Lambda$,
--   $$-\frac{1}{2(2\pi)^3}\int_{\lambda\le|\mathbf q|\le\Lambda}\frac{d^3q}{|\mathbf q|}\ \sum_{n,m}\frac{e_ne_m\eta_n\eta_m\,(p_n\cdot p_m)}{(p_n\cdot q)(p_m\cdot q)}=-A\ln(\Lambda/\lambda).$$
--
--   This is Eq. (2.13): the real part of the virtual infrared-photon exponent in (2.12), coming from the $i\pi\delta(q^2)$ part of the photon propagator, depends on the cutoffs only through $\ln(\Lambda/\lambda)$, giving the factor $(\lambda/\Lambda)^A$ of Eq. (2.18).
--
--   **Formalization Note** The paper writes the left side as $-\frac{1}{2(2\pi)^3}\int_\lambda^\Lambda d^4q\,\delta(q^2)\sum\cdots$. Performing the $q^0$ integration against $\delta(q^2)$ (the integrand is even under $q\to-q$) gives exactly the three-dimensional integral above over the shell $\lambda\le|\mathbf q|\le\Lambda$ with $q^0=|\mathbf q|$; the formal statement uses this three-dimensional form.
-- source:
--   S. Weinberg, Infrared Photons and Gravitons, Phys. Rev. 140, B516 (1965), https://doi.org/10.1103/PhysRev.140.B516, p. B518, Sec. II.3, Eqs. (2.13)–(2.15)

import Definitions.Def_Weinberg1965_Defs

namespace Weinberg1965

theorem photon_log_cutoff {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (p : ι → Vec3) (e η : ι → ℝ)
    (hm : ∀ n, 0 < m n) (hη : ∀ n, η n = 1 ∨ η n = -1)
    (lam Λ : ℝ) (hlam : 0 < lam) (hlamΛ : lam < Λ) :
    -(1 / (2 * (2 * Real.pi) ^ 3)) *
        ∫ q in {q : Vec3 | lam ≤ ‖q‖ ∧ ‖q‖ ≤ Λ}, (1 / ‖q‖) *
          ∑ n, ∑ k, e n * e k * η n * η k * mdot (m n) (p n) (m k) (p k) /
            (mdotNull (m n) (p n) q * mdotNull (m k) (p k) q)
      = -(photonIndex m p e η) * Real.log (Λ / lam) := by
  sorry

end Weinberg1965
