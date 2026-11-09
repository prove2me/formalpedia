-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_dyadic_verifiers
-- name    : QMAPerfectCompleteness.Main.dyadic_verifiers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:58.976283+00:00
-- url     : https://prove2.me/theorems/59b0898d-1653-4237-8027-ac9246b133b6
-- title:
--   Lemma 3.1 — QMA is unchanged over the gate set $\mathcal G_2$
-- statement:
--   Every QMA verifier can be compiled into the gate set $\mathcal G_2=\{X,\mathrm{CNOT},\mathrm{Toffoli},H\otimes H\}$ with the same completeness and soundness:
--
--   $$
--   \mathrm{QMA}=\mathrm{QMA}_{\mathcal G_2}(2/3,1/3).
--   $$
--
--   This is an equality of classes of promise problems, so both inclusions are claimed, with polynomial-time generation of the verifiers. The quantified proofs remain arbitrary complex density matrices, even though circuits over $\mathcal G_2$ have real matrices. The result gives the exact arithmetic control on the acceptance operator on which the rest of the construction rests.
--
--   Differences from the source:
--   - encoding: QMA is $\mathrm{QMA}_{\mathcal G}(2/3,1/3)$ for any universal gate set $\mathcal G$, well defined by Solovay-Kitaev and amplification → the fixed gate set $\{H,\Lambda(P)\}$; reason: it is the universal set the source's proof of Lemma 3.1 starts from, and the source states that the choice does not matter
--   - encoding: a polynomial-time algorithm maps $x$ to a verifier $V_x$ → a multi-stack machine (Turing.TM2ComputableInPolyTime) outputs a self-delimiting code of $V_x$ with every number in unary; gate sets are lists of exact unitary matrices, without the approximability clause of §2; reason: all numbers in a polynomial-size circuit are polynomially bounded, so unary and binary codes define the same class, and the three gate sets used here have explicitly computable entries
-- source:
--   Sabee Grewal, Dorian Rudolph, QMA has perfect completeness, STOC 2027 submission #490 (October 2026), p. 7, Lemma 3.1

import Definitions.Def_QMAPerfectCompleteness_Main_Classes

namespace QMAPerfectCompleteness.Main

/-- Lemma 3.1 (p. 7): `QMA = QMA_{𝒢₂}(2/3, 1/3)`. -/
theorem dyadic_verifiers : QMA = QMAClass gatesG2 (2 / 3) (1 / 3) := by sorry

end QMAPerfectCompleteness.Main
