-- Prove2me | Theorems.Thm_Weinberg1965_graviton_massless_limit
-- name    : Weinberg1965.graviton_massless_limit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T23:11:11.208997+00:00
-- url     : https://prove2.me/theorems/215e2714-c9af-45fb-89cd-213d0e0491dd
-- title:
--   Eqs. (3.4)–(3.5) — soft-graviton collinear divergences cancel for a massless line
-- statement:
--   Let the external lines $n$ of a process have three-momenta $\mathbf p_n$ and signs $\eta_n=\pm1$. Single out one line $1$ with $m_1=0$ and $\mathbf p_1\ne\mathbf 0$, and let all other lines be massive, $m_n>0$ for $n\ne1$. Assume energy–momentum conservation for this configuration,
--   $$\sum_n\eta_n\mathbf p_n=\mathbf 0,\qquad\sum_n\eta_nE_n=0\quad(E_1=|\mathbf p_1|).$$
--   Let $B(\mu)$ denote the infrared-graviton exponent (2.24) computed with the mass of line $1$ replaced by $\mu>0$ (keeping $\mathbf p_1$ and all other data fixed). Then $B(\mu)$ has a finite limit as $\mu\to0^+$.
--
--   This is the statement of Sec. III: although each term of (2.26) with $n$ or $m$ equal to $1$ contains a divergence proportional to $\ln m_1$ (from $\mathbf q$ parallel to $\mathbf p_1$), energy and momentum conservation make the total coefficient of $\ln m_1$ vanish, Eq. (3.5), so hard massless particles do not spoil the soft-graviton formulas.
--
--   **Formalization Note** The paper's “let $m_1\to0$ holding $\mathbf p_1$ fixed” is encoded as the one-sided limit $\mu\to0^+$ with the mass of line $1$ set to $\mu$; conservation is imposed at the massless configuration, which is where the paper uses it in (3.5). The contrasting non-cancellation for photons is the separate milestone for Eq. (3.3).
-- source:
--   S. Weinberg, Infrared Photons and Gravitons, Phys. Rev. 140, B516 (1965), https://doi.org/10.1103/PhysRev.140.B516, pp. B521–B522, Sec. III, Eqs. (3.1), (3.4)–(3.5)

import Definitions.Def_Weinberg1965_Defs

namespace Weinberg1965

theorem graviton_massless_limit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ℝ) (m : ι → ℝ) (p : ι → Vec3) (η : ι → ℝ) (i₁ : ι)
    (hm₁ : m i₁ = 0) (hm : ∀ n, n ≠ i₁ → 0 < m n) (hp₁ : p i₁ ≠ 0)
    (hη : ∀ n, η n = 1 ∨ η n = -1)
    (hmom : ∑ n, η n • p n = 0)
    (henergy : ∑ n, η n * energy (m n) (p n) = 0) :
    ∃ L : ℝ, Filter.Tendsto (fun μ : ℝ => gravitonIndex G (Function.update m i₁ μ) p η)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  sorry

end Weinberg1965
