-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_shadow_operator_inequality
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.shadow_operator_inequality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:42:09.936992+00:00
-- url     : https://prove2.me/theorems/b4917bfd-2248-40a1-8576-a4f45c1e4ab4
-- title:
--   Example 13 / Eq.(48): shadow operator inequality
-- statement:
--   Let $n\ge0$, $d_j\ge1$, and let $\rho$ be a density matrix on $H=\bigotimes_j\mathbb C^{d_j}$, meaning $\rho\ge0$ and $\operatorname{tr}\rho=1$. For $S\subseteq[n]$, let $\rho_S=\operatorname{tr}_{S^c}\rho$ and let $\iota_S(B)$ embed $B$ in its original factor positions with identities on $S^c$. For every $T\subseteq[n]$,
--
--   $$\sum_{S\subseteq[n]}(-1)^{|S\cap T|}\,\iota_S(\rho_S)\ge0.$$
--
--   All partial traces are unnormalized. This is the shadow operator inequality, including the scalar empty-party case.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 12, Example 13 / Eq.(48): shadow operator inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Example 13, Eq.48 (PDF p.12). Ordinary trace and identity-complement
embeddings, with no denominator involving local dimensions. -/
theorem shadow_operator_inequality {n : ℕ} (dims : Fin n → ℕ)
    (hdims : ∀ j, 0 < dims j) (T : Finset (Fin n))
    (rho : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ)) (hrho : QAlgorithms.IsDensityMatrix rho) :
    (shadow dims T rho).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
