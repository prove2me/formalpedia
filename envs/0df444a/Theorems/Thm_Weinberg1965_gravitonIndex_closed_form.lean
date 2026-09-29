-- Prove2me | Theorems.Thm_Weinberg1965_gravitonIndex_closed_form
-- name    : Weinberg1965.gravitonIndex_closed_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T23:06:04.497566+00:00
-- url     : https://prove2.me/theorems/0bcac0f0-c524-45ee-ac0d-e7b9f56cba4e
-- title:
--   Eq. (2.26) — closed form of the infrared-graviton exponent $B$
-- statement:
--   Let $G\in\mathbb R$ and let the external lines $n$ of a process have masses $m_n>0$, three-momenta $\mathbf p_n$ and signs $\eta_n=\pm1$ ($+1$ outgoing, $-1$ incoming). Let $\beta_{nm}$ be the relative velocity (2.17). Then the solid-angle integral (2.24) of the graviton angular function (2.25) is
--   $$B=\frac{G}{2\pi}\sum_{n,m}\eta_n\eta_mm_nm_m\,\frac{1+\beta_{nm}^2}{\beta_{nm}(1-\beta_{nm}^2)^{1/2}}\ln\Bigl(\frac{1+\beta_{nm}}{1-\beta_{nm}}\Bigr)=\frac{G}{\pi}\sum_{n,m}\eta_nm_n\eta_mm_m\,f(\beta_{nm}),$$
--   with $f(\beta)=\frac{1+\beta^2}{2\beta(1-\beta^2)^{1/2}}\ln\frac{1+\beta}{1-\beta}$ as in (4.5)–(4.6), extended by $f(0)=1$ (the value needed for the diagonal terms $n=m$).
--
--   $B$ is the exponent that governs soft-graviton physics in an arbitrary collision: the virtual-graviton factor $(\lambda/\Lambda)^B$ (2.27), the soft-graviton emission rate $(E/\Lambda)^Bb(B)\Gamma^0$ (2.52), and the soft gravitational power spectrum $E\,d\Gamma=B\,\Gamma^0\,dE$ (2.53) used in Sec. IV to estimate thermal gravitational radiation from the sun.
--
--   **Formalization Note** The right-hand side is written in the form (4.5), which the paper states is Eq. (2.26) rewritten. The printed exponent $1/2$ on the logarithm's argument in (4.6) is not used (see the definitions item).
-- source:
--   S. Weinberg, Infrared Photons and Gravitons, Phys. Rev. 140, B516 (1965), https://doi.org/10.1103/PhysRev.140.B516, p. B519, Sec. II.3, Eqs. (2.24)–(2.26); equivalently p. B522, Eqs. (4.5)–(4.6)

import Definitions.Def_Weinberg1965_Defs

namespace Weinberg1965

theorem gravitonIndex_closed_form {ι : Type*} [Fintype ι]
    (G : ℝ) (m : ι → ℝ) (p : ι → Vec3) (η : ι → ℝ)
    (hm : ∀ n, 0 < m n) (hη : ∀ n, η n = 1 ∨ η n = -1) :
    gravitonIndex G m p η =
      (G / Real.pi) *
        ∑ n, ∑ k, η n * η k * m n * m k * fWeinberg (relVel (m n) (p n) (m k) (p k)) := by
  sorry

end Weinberg1965
