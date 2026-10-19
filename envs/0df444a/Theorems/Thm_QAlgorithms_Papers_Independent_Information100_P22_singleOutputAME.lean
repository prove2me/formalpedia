-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_singleOutputAME
-- name    : QAlgorithms.Papers.Independent.Information100.P22.singleOutputAME
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:51:43.685508+00:00
-- url     : https://prove2.me/theorems/c378baee-026d-4a88-a44d-c63b1bdeaf99
-- title:
--   Proposition 1: Global single-output characterization
-- statement:
--   Let $k\ge1$, $m=1$, let $R$ be a normalized pure resource, and let $U$ be any unitary on $AS$ acting identically on $N$. Put $d=2^k$ and form its actual normalized encoded Choi vector $\Omega$ on the reference, transformed source, signal and key. Then
--   $$[S\text{ perfectly concealed and }SN\text{ exactly recoverable}]\iff\Omega\text{ is AME}(4,d).$$
--   Here AME means that all six two-party marginals are $I/d^2$. Every such realization has $\rho_S=\rho_N=I/d$. A realization exists precisely when $k\ge2$; the qubit case $k=1$ is impossible. This identifies the unrestricted single-output boundary.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 5, Proposition 1: Global single-output characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Proposition 1, PDF p.5, proof pp.24–25. Equivalence uses the actual encoded Choi vector. -/
theorem singleOutputAME (k : ℕ) (hk : 1 ≤ k)
    (R : EuclideanSpace ℂ (Signals 1 k × Signals 1 k)) (hR : IsState R)
    (U : Matrix.unitaryGroup (Qubits k × Signals 1 k) ℂ) :
    ((Concealed R (U : Op _) 0 ∧ AllRecoverable R (U : Op _)) ↔ AMEFour (omegaFour R (U : Op _))) ∧
    ((Concealed R (U : Op _) 0 ∧ AllRecoverable R (U : Op _)) →
      rhoS R = mixed (Signals 1 k) ∧ rhoN R = mixed (Signals 1 k)) ∧
    ((∃ Rnew : EuclideanSpace ℂ (Signals 1 k × Signals 1 k), IsState Rnew ∧
      ∃ V : Matrix.unitaryGroup (Qubits k × Signals 1 k) ℂ,
        Concealed Rnew (V : Op _) 0 ∧ AllRecoverable Rnew (V : Op _)) ↔ 2 ≤ k) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
