-- Prove2me | Theorems.Thm_QuantumOnePCA369_PauliPCA_projected_pauli_correct
-- name    : QuantumOnePCA369.PauliPCA.projected_pauli_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:08.71748+00:00
-- url     : https://prove2.me/theorems/0397c864-bf88-41c2-a179-622ec80a4c18
-- title:
--   Lemma 3.3 — Algorithm 2 computes the projected Paulis $\tilde U_s^\dagger\sigma_{x,A_rx+c_r}\tilde U_s$
-- statement:
--   Let $A_r\in\mathrm{Sym}_m(\mathbb F_2)$ and $c_r\in\mathbb F_2^m$ for $r<R$, and let $\tilde U_s$ be $2^m\times k_0$ complex matrices for $s\in\{0,1\}^\ell$. Then the matrices returned by Algorithm 2 are exactly
--   $$\pi_s^{(r)}(x)=\tilde U_s^\dagger\,\sigma_{x,A_rx+c_r}\,\tilde U_s,\qquad s\in\{0,1\}^\ell,\ r<R,\ x\in\mathbb F_2^m,$$
--   where $A_rx+c_r$ is computed over $\mathbb F_2$.
--
--   This is the affine Pauli sampling identity: along the random affine family $\{(x,A_rx+c_r)\}_x$ with symmetric $A_r$, all $2^m$ projected Paulis come out of two fast Walsh–Hadamard passes instead of $2^m$ separate products.
--
--   **Formalization Note** The phase $x\cdot A_rx$ lifts every entry of $A_r$ to $\{0,1\}\subset\mathbb Z$ before multiplying and is read mod 4 (see the Basic definition).
--
--   Differences from the source:
--   - reading: the phase i^{x·A_r x} with x·A_r x 'taken mod 4' → q_A(x) = Σ_{i,j} x_i A_ij x_j computed with every entry lifted to {0,1} ⊂ ℤ and read mod 4; the Pauli label A_r x + c_r is computed over F_2; reason: the nested expression is ambiguous; this is the reading under which the identity (x+y)·A(x+y) = x·Ax + 2x·Ay + y·Ay mod 4 on p. 9 holds (checked for every symmetric 2×2 matrix)
--   - generalization: partial unitaries Ũ_s of size 2^{n−ℓ} × k_0 with k_0 ≤ 2k → arbitrary complex 2^m × k_0 matrices Ũ_s, any k_0; reason: the identity is linear in Ũ_s and never uses orthonormality or the width bound; the source's case is a special case
--   - encoding: prefix s ∈ {0,1}^ℓ on the first ℓ qubits, Ũ_s of size 2^{n−ℓ} × k_0 → separate prefix and suffix lengths ℓ and m with ℓ + m = n; Ũ_s : 2^m × k_0; reason: m = n − ℓ without natural-number subtraction
--   - encoding: inputs n, ℓ, k, R of Algorithm 2 → inputs ℓ, m, k_0, R (n = ℓ + m); reason: k enters Algorithm 2 only through the width bound k_0 ≤ 2k
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 8, Lemma 3.3 (proof p. 9); Algorithm 2, p. 8

import Mathlib
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_ProjectedPauli

namespace QuantumOnePCA369.PauliPCA

theorem projected_pauli_correct (ℓ m k₀ R : ℕ) (A : Fin R → SymF2 m) (c : Fin R → Bits m)
    (U : Bits ℓ → Matrix (Bits m) (Fin k₀) ℂ) (r : Fin R) (s : Bits ℓ) (x : Bits m) :
    (alg2 ℓ m k₀ R A c U).val r s x =
      (U s).conjTranspose * pauli x ((A r).1.mulVec x + c r) * U s := by sorry

end QuantumOnePCA369.PauliPCA
