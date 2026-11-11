-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_decryption_execution
-- name    : PauliUnclonable531.Pauli.decryption_execution
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-10T09:02:28.328665+00:00
-- url     : https://prove2.me/theorems/19794b16-6d53-4a3e-81c9-a0857608f68c
-- title:
--   §3.1 — sequential local Pauli measurements implement decryption
-- statement:
--   Fix a nonidentity Pauli key $k=(x,z)$ on $n$ qubits. The §3.1 decryption procedure measures, one after another, each nonidentity position $j$ of $k$ in the eigenbasis of the local Pauli $\sigma_{(x_j,z_j)}\in\{X,Y,Z\}$, i.e. it applies the projective instrument $\{\Pi^{(j)}_{b}=\tfrac12(I+(-1)^{b}\sigma_{(x_j,z_j)})\text{ on wire }j\}_{b\in\{0,1\}}$ to the current unnormalized post-measurement state, and outputs the parity of the observed outcome bits.
--
--   For every operator $\sigma$ on the $n$-qubit space (in particular every density operator, including entangled ones) and every output bit $b$, the Born probability that this sequential procedure outputs $b$ equals the probability of outcome $b$ of the global two-outcome measurement $\{Q_{k,0},Q_{k,1}\}$:
--
--   $$\Pr[\text{procedure outputs } b\mid\sigma]=\operatorname{Re}\operatorname{Tr}\big[Q_{k,b}\,\sigma\big],\qquad Q_{k,b}=\tfrac12\big(I+(-1)^bP_k\big).$$
--
--   Thus decryption needs only single-qubit Pauli measurements and classical parity computation.
--
--   **Formalization Note.** The procedure is `decProgram k`, interpreted by `executeDec`, which sums over all outcome strings the traces of the unnormalized post-measurement states whose outcome parity equals $b$. The statement is proved for every complex matrix $\sigma$; the density hypothesis of the headline theorem is not needed.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits and real Born probabilities; reason: these are the same finite-dimensional objects after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026) / arXiv:2607.21551v4, §3.1, pp.16–17 (efficient decryption procedure); decryption effects of §3, p.15

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Ensemble

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

theorem decryption_execution (n : ℕ) (k : Key n) (σ : Op (Bits n)) (b : Fin 2) :
    operationalDec k σ b = born (decryptEffect k b) σ := by sorry

end PauliUnclonable531.Pauli
