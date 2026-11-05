-- Prove2me | Theorems.Thm_ShallowShadows_ShadowNorm_pauliInvariant_ensemble
-- name    : ShallowShadows.ShadowNorm.pauliInvariant_ensemble
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:32.902485+00:00
-- url     : https://prove2.me/theorems/b47203f7-2144-4a58-ae5c-20f6d2f1bfa9
-- title:
--   Appendix A: every $\mathcal U_d$ ($d = 0,1,\dots,\infty$) is a Pauli invariant ensemble of Cliffords
-- statement:
--   Let $n = 2m$. For every depth $d \in \{\infty, 0, 1, 2, \dots\}$, the shallow-shadow ensemble $\mathcal U_d$ is **Pauli invariant**: for every Pauli string $P$ and $U\sim\mathcal U_d$, the unitaries $PU$ and $UP$ have the same law as $U$ (up to global phase),
--
--   $$
--   \mu_d(PU) = \mu_d(UP) = \mu_d(U),
--   $$
--
--   and every unitary of $\mathcal U_d$ is Clifford.
--
--   Pauli invariance and the Clifford property are the only properties of $\mathcal U_d$ that the proofs of Lemma 13, Lemma 1 and Theorem 7 use.
--
--   Differences from the source:
--   - encoding: uniformly random single-qubit, two-qubit and n-qubit Clifford gates → uniform distribution on CliffordLabel k (k-qubit Cliffords modulo global phase), with [Fintype (CliffordLabel k)] as instance arguments; reason: every quantity depends on U only through X ↦ UXU†, the quotient is finite so the instances exist, and Fintype is a subsingleton so the uniform law does not depend on the instance
--   - encoding: n (even) qubits → n = 2m, m : ℕ; reason: same instances; m = 0 is the degenerate 0-qubit case
--   - encoding: every depth d ∈ {∞, 0, 1, …} → a conjunction: ∀ k : ℕ for brickwork m k, and globalClifford (2m) for d = ∞; reason: the two cases have different label types; both are stated in full
--   - reading: nearest-neighbour circular brickwork pattern, first and last qubit neighbours (p. 4, Fig. 1) → 0-based qubits; the paper's odd layers act on (2p, 2p+1), even layers on (2p+1, (2p+2) mod 2m); U = L_d ⋯ L_1 L_0; reason: fixed by Fig. 1's caption (layer 2 contains the pair (8, 1)) and by 'first applying … the 0th layer then for each layer i ∈ [d]'
--   - reading: for any Pauli S ∈ P_n … µ_d(PU) = µ_d(UP) = µ_d(U) → the laws of X ↦ (P^λU)X(P^λU)† and X ↦ (UP^λ)X(UP^λ)† equal the law of X ↦ UXU† (IsPauliInvariant), for every Pauli string P^λ; reason: the weights live on Cliffords modulo phase; the display names S and then uses P, read S = P
--   - generalization: the ensemble U_d is Pauli invariant → Pauli invariant and every positive-weight unitary is Clifford (IsCliffordPrimitive); reason: adds the fact that U_d is an 'ensemble of Clifford unitaries' (p. 4), which the sentence presupposes; it implies the source's claim
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, Appendix A, p. 10 (unnumbered, first sentence)

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_brickwork
import Definitions.Def_ShallowShadows_ShadowNorm_globalClifford
import Definitions.Def_ShallowShadows_ShadowNorm_IsPauliInvariant
import Definitions.Def_ShallowShadows_ShadowNorm_IsCliffordPrimitive

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, Appendix A, p. 10
(unnumbered): "for all `d` (including `d = 0` and `d = ∞`) the ensemble `𝒰_d` is Pauli invariant
in the sense that for any Pauli `S ∈ 𝒫_n`, and any Clifford `U ∈ 𝕌_d`, we have
`μ_d(PU) = μ_d(UP) = μ_d(U)`."

For every `m` (`n = 2m` qubits): every brickwork ensemble `𝒰_k`, `k ∈ ℕ` (`k = 0` included), and
the global Clifford ensemble `𝒰_∞` are Pauli invariant, and each consists of Clifford unitaries.

**Formalization Note.** Uniform Cliffords are uniform over Cliffords modulo global phase, with the
finiteness of the label types as instance arguments; Pauli invariance compares laws of
conjugation maps (`IsPauliInvariant`). The second conjunct of each case records that every unitary
of the ensemble is Clifford (`U_d ⊆ 𝒞_n`, §III). -/
theorem pauliInvariant_ensemble (m : ℕ) [Fintype (CliffordLabel 1)] [Fintype (CliffordLabel 2)]
    [Fintype (CliffordLabel (2 * m))] :
    (∀ k : ℕ, IsPauliInvariant (brickwork m k) ∧ IsCliffordPrimitive (brickwork m k)) ∧
      (IsPauliInvariant (globalClifford (2 * m)) ∧ IsCliffordPrimitive (globalClifford (2 * m))) := by sorry

end ShallowShadows.ShadowNorm
