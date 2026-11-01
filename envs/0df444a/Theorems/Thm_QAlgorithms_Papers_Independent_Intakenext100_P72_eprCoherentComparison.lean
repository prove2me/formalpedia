-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P72_eprCoherentComparison
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P72.eprCoherentComparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:45:30.275146+00:00
-- url     : https://prove2.me/theorems/50a72217-62bf-4d7b-9ea6-789b78ab16ea
-- title:
--   Signed EPR/coherent expressions: comparison and pure-loss equality
-- statement:
--   Let $V\ge1$, $G>0$, and $G\chi\ge|1-G|$. Write $P(G,\chi,V,s)=(G\chi+Gs)(G\chi+G/V)$ and $D_s=\tfrac12\log_2[1/P(G,\chi,V,s)]$. The EPR expression includes the probability $1/2$ of matching bases, while the coherent expression uses either basis:
--
--   $$
--   \begin{aligned}
--   E&=\tfrac12D_{1/V}=\frac14\log_2\frac1{(G\chi+G/V)^2}
--   =\frac12\log_2\frac1{G\chi+G/V},\\
--   C&=D_1=\frac12\log_2\frac1{(G\chi+G/V)(G\chi+G)}
--   =E-\frac12\log_2[G(1+\chi)]\le E.
--   \end{aligned}
--   $$
--
--   Equality holds precisely when $G\le1$ and $G\chi=1-G$. On that pure-loss branch,
--
--   $$
--   C=E=\frac12\log_2\frac1{1-G(1-1/V)}\ge0.
--   $$
--
--   The comparison includes physical amplification. Equality concerns signed expressions before clipping at zero; at $V=1$ the pure-loss expression is zero. Identifying these expressions with measured information is the separate deferred node (45)–(48).
-- source:
--   Reverse reconciliation protocols for quantum cryptography with continuous variables, arXiv:quant-ph/0204127v1, PDF p. 5, IV.A, (54)–(58): EPR/coherent information rates and equality case

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P72

noncomputable section

open Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P72

/-- Grosshans--Grangier, PDF p.5, IV.A, (54)--(58).
The denominator in (54), inspected in the PDF, is (G*chi+G/V)^2.
Comparison and equality concern signed model expressions before clipping;
physical amplifiers are included, with pure loss confined to G≤1. -/
theorem eprCoherentComparison
    (G chi V : ℝ) (hG : 0 < G) (hV : 1 ≤ V)
    (hphysical : |1 - G| ≤ G * chi) :
    eprExpression G chi V = (1 / 4 : ℝ) *
      Real.logb 2 (1 / (G * chi + G / V) ^ 2) ∧
    eprExpression G chi V = (1 / 2 : ℝ) * Real.logb 2 (1 / (G * chi + G / V)) ∧
    coherentExpression G chi V = (1 / 2 : ℝ) *
      Real.logb 2 (1 / ((G * chi + G / V) * (G * chi + G))) ∧
    coherentExpression G chi V = eprExpression G chi V -
      (1 / 2 : ℝ) * Real.logb 2 (G * (1 + chi)) ∧
    coherentExpression G chi V ≤ eprExpression G chi V ∧
    (coherentExpression G chi V = eprExpression G chi V ↔
      G ≤ 1 ∧ G * chi = 1 - G) ∧
    (G ≤ 1 → G * chi = 1 - G →
      eprExpression G chi V = lossExpression G V ∧
      coherentExpression G chi V = lossExpression G V ∧
      0 ≤ lossExpression G V) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P72

end
