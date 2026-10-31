-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_choi_isomorphism
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.choi_isomorphism
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:39:46.537177+00:00
-- url     : https://prove2.me/theorems/bfb27d3e-3459-4040-800a-4bd512dda093
-- title:
--   §2.6.4 (2.68)–(2.72): Choi–Jamiołkowski isomorphism
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces.
--
--   In finite dimensions, use the UNNORMALIZED maximally entangled vector Ψ to define the Choi matrix and the actual inverse map. CP iff Choi≥0; TP iff Tr_B Choi=I_Aprime; unital iff Tr_Aprime Choi=I_B.
--
--   $$
--   \Gamma(\mathcal E)_{(i,b),(j,b^\prime)}=\mathcal E(|i\rangle\langle j|)_{b,b^\prime},\quad\mathcal E\text{ CP}\iff\Gamma(\mathcal E)\ge0,\quad\mathcal E\text{ TP}\iff\operatorname{Tr}_B\Gamma(\mathcal E)=I_A.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 37, §2.6.4 (2.68)–(2.72): Choi–Jamiołkowski isomorphism

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#2.choi
§2.6.4 (2.68)-(2.72), PDF pp.37-38.
Printed: I_B tensor rho_Aprime^T in (2.69). Changed: rho_Aprime^T tensor I_B.
Why: the Choi matrix has register order Aprime,B; the entrywise inverse retains its transpose pairing. -/
theorem choi_isomorphism [Nonempty I] [Nonempty J] (E : paperMat I →ₗ[ℂ] paperMat J) :
    (∀ r : paperMat I, inverseChoi (paperChoi E) r = E r) ∧
    (∀ G : paperMat (I × J), (fun x y : I × J => inverseChoi G (Matrix.single x.1 y.1 1) x.2 y.2) = G) ∧
    (∀ G : paperMat (I × J), ∃ F : paperMat I →ₗ[ℂ] paperMat J, (∀ r, F r = inverseChoi G r) ∧ paperChoi F = G) ∧
    (QAlgorithms.Entanglement.IsCompletelyPositive E ↔ (paperChoi E).PosSemidef) ∧
    ((∀ r : paperMat I, (E r).trace = r.trace) ↔ traceRight (paperChoi E) = 1) ∧
    (E 1 = 1 ↔ traceLeft (paperChoi E) = 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
