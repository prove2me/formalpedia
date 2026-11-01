-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P93_cat_joint_law
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P93.cat_joint_law
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:35:28.385414+00:00
-- url     : https://prove2.me/theorems/59f858b2-f40b-4bcd-83ec-0e6bfd705c24
-- title:
--   Equation (6): exact logical-Pauli and specific-syndrome joint distribution
-- statement:
--   Let $p_x,p_y,p_z\ge0$, $p_x+p_y+p_z\le1$, and $p_I=1-p_x-p_y-p_z$. Apply this Pauli law independently to all $m=k+1\ge1$ physical qubits of the cat code. For a specified syndrome string $s\in\{0,1\}^k$ of weight $r$, let $J(u,v,s)$ be the probability, summed over physical error strings, of logical Pauli $X^uZ^v$ and syndrome $s$. Set $a=r,b=m-r$ when $u=0$, and $a=m-r,b=r$ when $u=1$. Then
--
--   $$
--   J(u,v,s)=\frac{(p_x+p_y)^a(1-p_x-p_y)^b+(-1)^v(p_x-p_y)^a(1-p_x-p_y-2p_z)^b}{2}.
--   $$
--
--   This is the law of one syndrome string, so no binomial coefficient occurs. It supplies the full joint Pauli law, including correlated amplitude and phase errors.
-- source:
--   Degenerate Quantum Codes for Pauli Channels, arXiv:quant-ph/0604107v2, PDF p. 2, Equation (6): exact logical-Pauli and specific-syndrome joint distribution

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P93

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P93

open QAlgorithms

open scoped BigOperators ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Smith--Smolin, PDF p.2, Eq.(6): one specific syndrome's joint law, with
piecewise nonnegative exponents equivalent to u(m-2r)+r and (1-u)(m-2r)+r. -/
theorem cat_joint_law (k : ℕ) (px py pz : ℝ)
    (hx : 0 ≤ px) (hy : 0 ≤ py) (hz : 0 ≤ pz) (hsum : px + py + pz ≤ 1)
    (u v : Bool) (s : Qubits k) :
    catLogicalSyndromeMass k px py pz u v s =
      ((px + py) ^ amplitudeCount k u s * (1 - px - py) ^ noAmplitudeCount k u s +
        (if v then (-1 : ℝ) else 1) * (px - py) ^ amplitudeCount k u s *
          (1 - px - py - 2 * pz) ^ noAmplitudeCount k u s) / 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P93

end
