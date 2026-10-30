-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P41_blind_compression
-- name    : QAlgorithms.Papers.Independent.Advance50.P41.blind_compression
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:11:23.094817+00:00
-- url     : https://prove2.me/theorems/7088bba0-7ae1-4f3b-81a4-ed3e20863def
-- title:
--   Blind compression and the irreducible Schumacher limit
-- statement:
--   Let $\mathcal E=\{p(x),|\psi_x\rangle^A\otimes|\sigma_x\rangle^C\}$ be a countably supported ensemble with strictly positive probabilities summing to one and normalized pure vectors on finite-dimensional complex systems $A,C$. Let $Y=y(X)$ be the canonical orthogonal irreducible-component label of the joint $AC$ ensemble. Entropies $S$ use base-two logarithms and refer to the resulting source and its canonical $Y$ extension.
--
--   A block code uses arbitrary CPTP maps $A^nC^nA_0\to\widehat C^nM$ and $MB_0\to\widehat A^n$, fixed independently of the inaccessible input word, and an initial maximally entangled state of local dimension $K_n\ge1$. For every positive block length $n$, $1\le d_n=\dim M\le(\dim A)^n$. Write $Q_n=\log_2 d_n/n$, $E_n=\log_2 K_n/n$, and $F_n$ for the average joint root fidelity with the original $A^nC^n$ letters.
--
--   Suppose all side-information pure densities are identical, allowing arbitrary global phases of their representing vectors. Then
--   $$q_*=\tfrac12\bigl(S(A)+S(AY)-S(Y)\bigr)=S(A)-\tfrac12S(Y).$$
--   Every successful code sequence with limiting quantum rate $Q$ has $Q\ge q_*$, irrespective of its entanglement rates. There is one successful sequence attaining simultaneously $Q=q_*$ and $E=S(Y)/2$. Every successful sequence with finite limiting rates also obeys
--   $$Q+E\ge S(A).$$
--   If the original ensemble is irreducible, then $Y$ is constant and $q_*=S(A)$.
--
--   This identifies precisely when entanglement lowers the blind quantum compression rate.
-- source:
--   Entanglement-Assisted Quantum Data Compression, arXiv:1901.06346v1, PDF p. 4, Corollary 7, continued p.5

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P41

open Filter

open scoped Topology BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A C : Type} [Fintype A] [Fintype C]

/-- Corollary 7, PDF pp.4,5: both blind entropy formulas, a minimum with
simultaneous E=S(Y)/2 attainment, the sum-rate converse, and the irreducible
Schumacher specialization. Identical side states means identical densities. -/
theorem blind_compression [Countable X] (s : ProductPureSource X A C) (hs : s.Valid)
    (hblind : s.Blind) :
    s.quantumCorner = (s.entropyA + s.entropyAY - s.entropyY) / 2 ∧
    s.quantumCorner = s.entropyA - s.entropyY / 2 ∧
    s.OptimalQuantumCorner (s.entropyA - s.entropyY / 2) (s.entropyY / 2) ∧
    s.SumRateConverse ∧
    (s.Irreducible → s.quantumCorner = s.entropyA) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P41

end
