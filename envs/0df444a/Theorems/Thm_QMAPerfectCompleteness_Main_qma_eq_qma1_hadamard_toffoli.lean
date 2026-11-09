-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_qma_eq_qma1_hadamard_toffoli
-- name    : QMAPerfectCompleteness.Main.qma_eq_qma1_hadamard_toffoli
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:23.904436+00:00
-- url     : https://prove2.me/theorems/83417b16-40bb-4dfb-ae5f-48e603bf2b4a
-- title:
--   Theorem 1.1 — $\mathrm{QMA}=\mathrm{QMA}_1^{HT}$
-- statement:
--   Every quantum Merlin–Arthur proof system can be made perfectly complete using only Hadamard and Toffoli gates:
--
--   $$
--   \mathrm{QMA}=\mathrm{QMA}_1^{HT},\qquad HT=\{H,\mathrm{Toffoli}\}.
--   $$
--
--   This is an equality of classes of binary promise problems. Here QMA has completeness $2/3$ and soundness $1/3$ over a universal gate set. A problem lies in $\mathrm{QMA}_1^{HT}$ if a polynomial-time algorithm maps each input to a verifier over $H$ and Toffoli such that on YES inputs some proof, an arbitrary complex density matrix on polynomially many qubits, is accepted with probability exactly $1$, and on NO inputs every proof is accepted with probability at most $1/2$.
--
--   The theorem resolves the question, open since Bravyi introduced $\mathrm{QMA}_1$, of whether perfect completeness changes the power of QMA. It also shows that $HT$ is universal for $\mathrm{QMA}_1$, a question for which approximate synthesis gives no answer because approximating a gate can lower an acceptance probability of one.
--
--   Differences from the source:
--   - encoding: QMA is $\mathrm{QMA}_{\mathcal G}(2/3,1/3)$ for any universal gate set $\mathcal G$, well defined by Solovay-Kitaev and amplification → the fixed gate set $\{H,\Lambda(P)\}$; reason: it is the universal set the source's proof of Lemma 3.1 starts from, and the source states that the choice does not matter
--   - encoding: a polynomial-time algorithm maps $x$ to a verifier $V_x$ → a multi-stack machine (Turing.TM2ComputableInPolyTime) outputs a self-delimiting code of $V_x$ with every number in unary; gate sets are lists of exact unitary matrices, without the approximability clause of §2; reason: all numbers in a polynomial-size circuit are polynomially bounded, so unary and binary codes define the same class, and the three gate sets used here have explicitly computable entries
-- source:
--   Sabee Grewal, Dorian Rudolph, QMA has perfect completeness, STOC 2027 submission #490 (October 2026), p. 2, Theorem 1.1; proof p. 11; Definition 2.1, p. 6

import Definitions.Def_QMAPerfectCompleteness_Main_Compiler

open Matrix

namespace QMAPerfectCompleteness.Main

/-- Theorem 1.1 (p. 2; proof p. 11): `QMA = QMA₁^{HT}`, as classes of promise problems. -/
theorem qma_eq_qma1_hadamard_toffoli : QMA = QMA1 gatesHT := by sorry

end QMAPerfectCompleteness.Main
