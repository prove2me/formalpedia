-- Prove2me | Theorems.Thm_SuperBAE_Restriction_product_4_6
-- name    : SuperBAE.Restriction.product_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:26.947214+00:00
-- url     : https://prove2.me/theorems/055da0cc-7f3d-4bc4-9871-b15657acffe9
-- title:
--   §4.1 R2, p. 18 (PDF 19) — multiplying the BAE for α_{k−1} and α_{k+1} under R1 gives (4.6)
-- statement:
--   In the setting of the $\mathfrak{gl}(M|N)$ Bethe ansatz equations (2.9) with $n=M-N>0$, let $\alpha_k$ satisfy **A1** ($\sigma_k\sigma_{k+1}=-1$) and **A2** ($2\le k\le d-2$), assume **R1** (the roots of types $k-1$ and $k+1$ coincide) and that the root family is regular. Then for every root $u$ of type $k-1$ (equivalently of type $k+1$):
--   $$(4.2)\text{ at }u \;\wedge\; (4.4)\text{ at }u \;\Longrightarrow\; (4.6)\text{ at }u,$$
--   where
--   $$\text{(4.6)}\quad \frac{\sigma_{k-1}\Lambda_{k-1}(u)}{\sigma_{k+2}\Lambda_{k+2}(u)} = -\frac{Q_{k-2}(u)\,Q_{k-1}(u+\sigma_{k+2})\,Q_{k+2}(u-\sigma_{k+2})}{Q_{k-2}(u+\sigma_{k-1})\,Q_{k-1}(u-\sigma_{k-1})\,Q_{k+2}(u)} .$$
--
--   This is step **R2** of the restriction: in the product of the two equations the roots of type $k$ drop out, leaving an equation of the form (4.2) with $k$ replaced by $k+2$.
--
--   **Formalization Note.** Regularity is added; it guarantees that the factors $Q_k(u)$, $Q_k(u-\sigma_k)$, $Q_{k-1}(u+\sigma_k)$ that cancel in the product are nonzero. The standing assumption $N<M$ (p. 7) is kept; it is not used.
-- source:
--   Candu, Continuum Limit of gl(M|N) Spin Chains, arXiv:1012.0050v1, p. 18 (PDF 19), §4.1, R2, eq. (4.6)

import Mathlib
import Definitions.Def_SuperBAE_Restriction_Model

namespace SuperBAE.Restriction

theorem product_4_6 (L : ℕ) (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) (k : ℕ)
    (hA1 : odd k ≠ odd (k + 1)) (hA2k : 2 ≤ k) (hA2d : k + 2 ≤ d)
    (hn : numOdd odd d < numEven odd d)
    (hR1 : roots (k - 1) = roots (k + 1)) (hreg : Regular L odd d roots) :
    ∀ u ∈ roots (k - 1), eq4_2 L odd d roots k u → eq4_4 L odd d roots k u →
      eq4_6 L odd d roots k u := by sorry

end SuperBAE.Restriction
