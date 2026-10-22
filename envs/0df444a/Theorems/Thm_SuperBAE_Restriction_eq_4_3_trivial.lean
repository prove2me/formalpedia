-- Prove2me | Theorems.Thm_SuperBAE_Restriction_eq_4_3_trivial
-- name    : SuperBAE.Restriction.eq_4_3_trivial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:22.553777+00:00
-- url     : https://prove2.me/theorems/71666cc9-798a-480f-a1ae-f0bd9b3af801
-- title:
--   §4.1, p. 18 (PDF 19) — under R1, the α_k equation (4.3) is trivially satisfied
-- statement:
--   In the setting of the $\mathfrak{gl}(M|N)$ Bethe ansatz equations (2.9) with $n=M-N>0$, let $\alpha_k$ satisfy **A1** ($\sigma_k\sigma_{k+1}=-1$) and **A2** ($2\le k\le d-2$), and assume **R1**: the Bethe roots of types $k-1$ and $k+1$ coincide,
--   $$\{u^{(k-1)}_j\}_{j=1}^{\nu^{(k-1)}} = \{u^{(k+1)}_j\}_{j=1}^{\nu^{(k+1)}} .$$
--   If the root family is regular, then every root $u$ of type $k$ satisfies (4.3),
--   $$1 = \frac{Q_{k-1}(u)\,Q_{k+1}(u+\sigma_k)}{Q_{k-1}(u+\sigma_k)\,Q_{k+1}(u)},$$
--   and hence the Bethe equation (2.9) of type $k$ at $u$, whatever the roots of type $k$ are.
--
--   This is why, after the identification R1, the roots of type $k$ impose no condition of their own.
--
--   **Formalization Note.** Regularity is added (nonzero denominators of (2.9) and nonzero $\Lambda_k(u)$); it is what makes the quotient in (4.3) equal to $1$ rather than Lean's junk value $0$. The standing assumption $N<M$ (p. 7) is kept; it is not used.
-- source:
--   Candu, Continuum Limit of gl(M|N) Spin Chains, arXiv:1012.0050v1, p. 18 (PDF 19), §4.1, R1 (4.5), "Indeed, eq. (4.3) is trivially satisfied because according to R1 one has Q_{k−1}(u) = Q_{k+1}(u)"

import Mathlib
import Definitions.Def_SuperBAE_Restriction_Model

namespace SuperBAE.Restriction

theorem eq_4_3_trivial (L : ℕ) (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) (k : ℕ)
    (hA1 : odd k ≠ odd (k + 1)) (hA2k : 2 ≤ k) (hA2d : k + 2 ≤ d)
    (hn : numOdd odd d < numEven odd d)
    (hR1 : roots (k - 1) = roots (k + 1)) (hreg : Regular L odd d roots) :
    ∀ u ∈ roots k, eq4_3 d odd roots k u ∧ bae L odd d roots k u := by sorry

end SuperBAE.Restriction
