-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_sufficient_pureConversion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.sufficient_pureConversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:34:53.665061+00:00
-- url     : https://prove2.me/theorems/f979a406-53c2-47fc-bf0e-97faa8a082c0
-- title:
--   Theorem 7: sufficient pure-state conversion condition
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. A non-entangling map is completely positive and preserves the full separable positive cone. A channel is also trace preserving. Let $\psi$ and $\varphi$ be bipartite pure states, possibly on different registers, and let $\lambda_1>0$ be the largest squared Schmidt coefficient of $\psi$. For standard robustness $R$, if
--
--   $$1+R(\varphi)\le\frac1{\lambda_1},$$
--
--   then there exists a non-entangling channel $\Lambda$ such that $\Lambda(\psi)=\varphi$.
--
--   This is a sufficient condition for exact conversion.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 11, Theorem 7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- Theorem 7, PDF p.11: a sufficient conversion criterion. The denominator
is positive for every unit ket; the conclusion is not an equivalence. -/
theorem sufficient_pureConversion {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (psi : UnitBipartiteKet a b) (phi : UnitBipartiteKet c d)
    (hcriterion : 1 + standardStateRobustness phi.rho ≤ 1 / schmidtAt psi.ket 0) :
    ∃ L : Superop (Fin a × Fin b) (Fin c × Fin d),
      IsChannel L ∧ NE L ∧ L psi.rho = phi.rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
