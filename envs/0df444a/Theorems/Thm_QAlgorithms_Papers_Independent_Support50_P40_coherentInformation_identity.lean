-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P40_coherentInformation_identity
-- name    : QAlgorithms.Papers.Independent.Support50.P40.coherentInformation_identity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:05:33.995836+00:00
-- url     : https://prove2.me/theorems/17708afa-bcd5-4ba5-9ea1-8c63fd21582c
-- title:
--   Same-code output spectra, entropies, and coherent information
-- statement:
--   Fix an additive code encoding one qubit into $p\ge1$ physical qubits, with a normalized orthogonal logical basis $V|0\rangle,V|1\rangle$, a valid commuting stabilizer with $p-1$ independent generators and no $-I$, and complete compatible coset representatives $e_i,s_j$. Let $f\in[0,1]$, $g=(1-f)/3$, $a_i=P_f(e_i\bar S^\perp)$, and $b_{ij}=P_f(e_i s_j\bar S)$. Prepare the normalized vector $|\Omega\rangle=(|0\rangle_RV|0\rangle+|1\rangle_RV|1\rangle)/\sqrt2$. Pass only the physical code register through independent depolarization, obtaining $\rho_{RQ}$, and set $\rho_Q=\operatorname{Tr}_R\rho_{RQ}$.
--
--   Both outputs are density matrices. The vectors $v_{ib}=e_iV|b\rangle$ form an orthonormal basis, as do the generalized Bell vectors $B_{ij}=(I_R\otimes e_i s_j)|\Omega\rangle$. Their diagonalizations and entropies in bits are
--
--   $$
--   \rho_Q=\sum_{i,b}\frac{a_i}{2}|v_{ib}\rangle\langle v_{ib}|,\qquad
--   \rho_{RQ}=\sum_{i,j}b_{ij}|B_{ij}\rangle\langle B_{ij}|,
--   $$
--   $$
--   S(\rho_Q)=1+H(a),\qquad S(\rho_{RQ})=H(b),\qquad
--   \frac{S(\rho_Q)-S(\rho_{RQ})}{p}=q_C(f).
--   $$
--
--   The last quantity is the signed concatenation yield for this same code and input; no optimization over inputs is performed.
--
--   **Formalization Note** Printed Eq. (29) uses amplitudes $1/2$ instead of $1/\sqrt2$. Normalization, Eqs. (7)–(9), and Eq. (35) force the stated correction; independent moderation remains required.
-- source:
--   Quantum Channel Capacity of Very Noisy Channels, arXiv:quant-ph/9706061v3, PDF p. 14, Section IV, Eqs. (21)-(30): same-code coherent-information identity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

/-- PDF pp.14--15, Eqs.(21)--(30): both diagonalizations, both entropy
identities, and coherent information per use for this same code and input.
Eq.(29)'s printed `1/2` amplitudes are corrected as explained in `codeBellInput`.
Neither an input maximization nor a general capacity formula is asserted. -/
theorem coherentInformation_identity {m : ℕ} (C : InnerCode m) (T : CosetChoices C)
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    IsState (codeBellInput C) ∧ IsDensityMatrix (outputQ C f) ∧ IsDensityMatrix (outputRQ C f) ∧
    Orthonormal ℂ (fun ib : Qubits m × Bool => errorBasis C T ib.1 ib.2) ∧
    Orthonormal ℂ (fun ij : Qubits m × Pauli => bellBasis C T ij.1 ij.2) ∧
    outputQ C f = ∑ ib : Qubits m × Bool,
      ((syndromeMass C T f ib.1 / 2 : ℝ) : ℂ) • pureDensity (errorBasis C T ib.1 ib.2) ∧
    outputRQ C f = ∑ ij : Qubits m × Pauli,
      (jointMass C T f ij.1 ij.2 : ℂ) • pureDensity (bellBasis C T ij.1 ij.2) ∧
    vnEntropy (outputQ C f) = 1 + finiteEntropyBits (syndromeMass C T f) ∧
    vnEntropy (outputRQ C f) = finiteEntropyBits (fun ij : Qubits m × Pauli => jointMass C T f ij.1 ij.2) ∧
    (vnEntropy (outputQ C f) - vnEntropy (outputRQ C f)) / (m + 1) = signedYield C T f := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P40
