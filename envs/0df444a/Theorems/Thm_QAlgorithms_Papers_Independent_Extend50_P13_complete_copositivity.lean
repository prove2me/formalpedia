-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_complete_copositivity
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.complete_copositivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:43:43.347986+00:00
-- url     : https://prove2.me/theorems/7cc03929-3324-4833-9bea-4b32c4dabebb
-- title:
--   Proposition 15: complete copositivity
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. For $k=r+1\ge1$ and a partition $\lambda\vdash k$, let $T(\pi)$ permute tensor factors by $v_1\otimes\cdots\otimes v_k\mapsto v_{\pi^{-1}(1)}\otimes\cdots\otimes v_{\pi^{-1}(k)}$, and set $P_\lambda=\frac{\chi_\lambda(e)}{k!}\sum_{\pi\in S_k}\chi_\lambda(\pi^{-1})T(\pi)$ and $f_\lambda(X_1,\ldots,X_r)=\operatorname{tr}_{1\ldots r}[P_\lambda(X_1\otimes\cdots\otimes X_r\otimes I)]$. Here $\chi_\lambda$ is the character of the shape-labelled Specht representation, independently of $d$; shapes with more than $d$ rows are included. Define the complex-linear extension $\widetilde f_\lambda(Z)=\operatorname{tr}_{1\ldots r}[P_\lambda(Z\otimes I)]$ on the full joint-input matrix algebra. For every integer $m\ge1$ and every $Z\ge0$ on $(\mathbb C^d)^{\otimes r}\otimes\mathbb C^m$,
--
--   $$[(\widetilde f_\lambda\circ\theta)\otimes\operatorname{id}_m](Z)\ge0,$$
--
--   where $\theta$ transposes all input factors and leaves the ancillary factor unchanged. This is complete copositivity of the linearization, including its multilinear product-input specialization.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 13, Proposition 15: complete copositivity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Proposition 15, Eq.52 and the first equality in Eq.53 (PDF p.13).
Complete positivity is stated for the transposed linearization on the full
joint-input algebra, for every positive ancillary dimension m. -/
theorem complete_copositivity {d r : ℕ} (hd : 0 < d)
    (lambda : QAlgorithms.Schur.Partition (r+1) (r+1))
    (m : ℕ) (hm : 0 < m) (Z : (Matrix ((Fin r → Fin d) × Fin m) ((Fin r → Fin d) × Fin m) ℂ))
    (hZ : Z.PosSemidef) :
    (copositiveAmplification (centralProjector d lambda) m Z).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
