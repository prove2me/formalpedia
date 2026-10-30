-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P12_multipartite_positivity_iff
-- name    : QAlgorithms.Papers.Independent.Extend50.P12.multipartite_positivity_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:50:38.683497+00:00
-- url     : https://prove2.me/theorems/4f7ee056-dac2-4bcc-bb30-5bbcdbd03fa7
-- title:
--   Proposition 5: general multipartite block-positivity correspondence
-- statement:
--   Let $d,r,m\ge1$ be integers and set $k=r+m$. Let $P$ be any complex matrix on $(\mathbb C^d)^{\otimes k}$; no positivity, Hermiticity or normalization assumption is imposed on $P$. Define
--   $$
--   \Lambda(X_1,\ldots,X_r)=\operatorname{tr}_{1\cdots r}\!\left[P(X_1\otimes\cdots\otimes X_r\otimes I^{\otimes m})\right].
--   $$
--   Then
--   $$
--   \Lambda\text{ is positive}\ \Longleftrightarrow\
--   P\text{ is block-positive across }1|\cdots|r|[r+1,\ldots,k].
--   $$
--   Here positivity means that every tuple of PSD matrices $X_i\in M_d(\mathbb C)$ gives a PSD output, with unrestricted traces. Block positivity means that $\operatorname{tr}[P(X_1\otimes\cdots\otimes X_r\otimes C)]$ is real and nonnegative for all such $X_i$ and all PSD $C$ on the entire $m$-register output space. The partial trace is unnormalized.
--
--   This correspondence allows the output registers to be tested jointly, including by matrices entangled across output sites.
--
--   **Formalization Note** The final endpoint printed as $m$ in the partition is corrected to $k$, as forced by the output test in Eq. (36).
-- source:
--   Positive maps from the walled Brauer algebra, arXiv:2112.12738v3, PDF p. 6, Proposition 5, Eqs.(34)-(36)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P12

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P12

attribute [local instance] Classical.propDecidable

/-- Proposition 5, PDF p.6, Eqs.(34)-(36). Write k=r+m with r,m>=1. The printed
last block ends with "m"; the corrected endpoint is k, uniquely determined by
the m-output-register test C in Eq.(36). P is arbitrary: neither its positivity
nor its block positivity is assumed. Complex trace nonnegativity includes its
imaginary part being zero. -/
theorem multipartite_positivity_iff
    (d r m : ℕ) (hd : 0 < d) (hr : 0 < r) (hm : 0 < m)
    (P : Matrix (Fin (r + m) → Fin d) (Fin (r + m) → Fin d) ℂ) :
    PositiveMap (productInputContraction P) ↔ InputOutputBlockPositive P := by sorry

end QAlgorithms.Papers.Independent.Extend50.P12

end
