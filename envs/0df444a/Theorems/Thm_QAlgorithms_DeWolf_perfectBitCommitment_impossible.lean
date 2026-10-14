-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_perfectBitCommitment_impossible
-- name    : QAlgorithms.DeWolf.perfectBitCommitment_impossible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:43:18.930981+00:00
-- url     : https://prove2.me/theorems/5f4b155d-7f24-4a2f-b2dc-100fc0f4675c
-- title:
--   Perfect quantum bit commitment is impossible: perfect concealing implies no binding
-- statement:
--   This is the impossibility of perfect quantum bit commitment.
--
--   In de Wolf's model, a quantum bit-commitment protocol is represented by the two joint pure states $|\phi_0\rangle, |\phi_1\rangle \in \mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B}$ that Alice and Bob share at the end of the commit phase when Alice honestly commits to the bit $b = 0$ or $b = 1$. Here $\mathbb{C}^{d_A}$ is Alice's space and $\mathbb{C}^{d_B}$ is Bob's. Restricting to pure states loses no generality. The protocol is *perfectly concealing* if Bob's reduced density matrix does not depend on $b$, where $\operatorname{Tr}_A$ is the partial trace over Alice's register.
--
--   Let $d_A, d_B \ge 0$ and let $|\phi_0\rangle, |\phi_1\rangle$ be unit vectors in $\mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B}$ with
--
--   $$
--   \operatorname{Tr}_A\big(|\phi_0\rangle\langle\phi_0|\big) = \operatorname{Tr}_A\big(|\phi_1\rangle\langle\phi_1|\big).
--   $$
--
--   Then there is a unitary $U$ on Alice's space $\mathbb{C}^{d_A}$ such that
--
--   $$
--   (U \otimes I)\,|\phi_0\rangle = |\phi_1\rangle.
--   $$
--
--   So after committing to $0$, Alice can turn the joint state into the honest commitment to $1$ by acting on her own register only. The protocol is then not binding at all, and no quantum bit-commitment protocol is both perfectly concealing and perfectly binding.
--
--   **Formalization Note** Alice's space is indexed by `Fin dA` and Bob's by `Fin dB`. The joint space is indexed by `Fin dA × Fin dB` with Alice's register first. $\operatorname{Tr}_A(|\phi\rangle\langle\phi|)$ is `traceLeft (pureDensity phi)`, and $U \otimes I$ is `Matrix.kronecker U 1` with $U$ in `Matrix.unitaryGroup`. When $d_A = 0$ or $d_B = 0$ no unit vector exists, so the statement is vacuous in those cases, as in the source.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 172, §18.4. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Information
set_option autoImplicit false

namespace QAlgorithms.DeWolf

/-- de Wolf §18.4 (PDF pp. 171–172), unnumbered: a perfectly concealing quantum bit commitment
cannot be binding at all. For all dimensions `d_A, d_B` and all unit vectors
`|ϕ_0⟩, |ϕ_1⟩ ∈ ℂ^{d_A} ⊗ ℂ^{d_B}` (Alice's factor first) with equal reduced states on Bob's side,
`Tr_A(|ϕ_0⟩⟨ϕ_0|) = Tr_A(|ϕ_1⟩⟨ϕ_1|)`, there is a unitary `U` on Alice's space `ℂ^{d_A}` with
`(U ⊗ I)|ϕ_0⟩ = |ϕ_1⟩`. -/
theorem perfectBitCommitment_impossible (dA dB : ℕ)
    (phi0 phi1 : EuclideanSpace ℂ (Fin dA × Fin dB)) (h0 : IsState phi0) (h1 : IsState phi1)
    (hconceal : traceLeft (pureDensity phi0) = traceLeft (pureDensity phi1)) :
    ∃ U ∈ Matrix.unitaryGroup (Fin dA) ℂ,
      act (Matrix.kronecker U (1 : Matrix (Fin dB) (Fin dB) ℂ)) phi0 = phi1 := by
  sorry

end QAlgorithms.DeWolf
