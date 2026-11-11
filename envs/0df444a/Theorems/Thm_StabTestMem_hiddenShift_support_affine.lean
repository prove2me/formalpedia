-- Prove2me | Theorems.Thm_StabTestMem_hiddenShift_support_affine
-- name    : StabTestMem.hiddenShift_support_affine
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:09.466986+00:00
-- url     : https://prove2.me/theorems/ee2fdd92-499a-4e44-913c-81b29bb11b4d
-- title:
--   Lemma 4.3 — completeness of the stabilizer hidden-shift sampler
-- statement:
--   Let $|\psi\rangle$ be a stabilizer state on $n=k+m$ qubits and $M_\psi$ the labels of the Paulis that stabilize it up to sign. Suppose partial Bell difference sampling outputs $(a,r)\in\mathbb F_2^{2k}\times\mathbb F_2^m$ (with positive probability). Then
--
--   1. there is $t^*\in\mathbb F_2^m$ with $(a_Xr,\,a_Zt^*)\in M_\psi$;
--   2. for every such $t^*$, with the phase choice $\beta=t^*\cdot r \pmod 2$, the output distribution $P^\beta_{a,r}$ of Algorithm 3 is supported on the graph of an affine function $\chi_{t^*,c}(s)=t^*\cdot s\oplus c$ for some $c\in\mathbb F_2$: every outcome $(s,b)$ of positive probability has $b=t^*\cdot s\oplus c$.
--
--   This is the completeness of the tester: on a stabilizer state, the hidden-shift samples always pass the affine-graph test for the right phase guess.
--
--   **Formalization Note** $M_\psi$ is the published `QuantumHMMR.stabilizerLabels` ($\{x: W_x|\psi\rangle=\pm|\psi\rangle\}$ with $W_{(a,b)}=\bigotimes_i i^{a_ib_i}X^{a_i}Z^{b_i}=P_{a,b}$).
--
--   Differences from the source:
--   - encoding: n qubits with m = n − k → k + m qubits; reason: the same instances; the paper's m := n − k
--   - encoding: stabilizer state: a maximal Abelian subgroup of Paulis with P|ψ⟩ = ±|ψ⟩ → a unit vector fixed by a commuting subgroup of the Pauli group of order 2^n not containing −I; reason: the signs χ(u) are absorbed into the group elements ±P_u; same states
--   - reading: there is t∗ such that (a_X r, a_Z t) ∈ M_ψ → (a_X r, a_Z t∗) ∈ M_ψ; reason: t is unbound in the printed sentence; the proof uses t∗
--   - generalization: the phase choice β = t∗ · r for the t∗ of the first sentence → for every t∗ with (a_X r, a_Z t∗) ∈ M_ψ; reason: the proof uses only this membership; specializing to the paper's t∗ gives the printed claim
--   - encoding: partial Bell difference sampling outputs (a, r) → 0 < Q^k_ψ(a, r); reason: an output that occurs has positive probability
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 4.3, p. 26

import Definitions.Def_StabTestMem_pbds
import Definitions.Def_StabTestMem_hsProb
import Definitions.Def_QuantumHMMR_stabilizerLabels
import Definitions.Def_QAlgorithms_Defs_StabilizerLearning

namespace StabTestMem

open QAlgorithms

/-- **Lemma 4.3: completeness of the stabilizer hidden-shift sampler.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 4.3, p. 26:
"Let |ψ⟩ be a stabilizer state, and let M_ψ ≤ F_2^{2n} be the subspace of Pauli labels that
stabilize |ψ⟩ up to signs. Suppose partial Bell Difference sampling outputs (a, r) ∈ F_2^{2k} ×
F_2^m. Then there is t∗ ∈ F_2^m such that (a_X r, a_Z t) ∈ M_ψ. Moreover, for the phase choice
β = t∗ · r (mod 2), the output distribution of Algorithm 3 is supported on Graph(χ_{t∗,c}) for some
c ∈ F_2."

For a stabilizer state `ψ` on `k + m` qubits and an outcome `(a, r)` of positive probability under
partial Bell difference sampling: (1) some completion `t` has `(a_X r, a_Z t) ∈ M_ψ`; (2) for every
such completion `t∗`, with `β = t∗·r mod 2`, every outcome `(s, b)` of Algorithm 3 of positive
probability satisfies `b = t∗·s ⊕ c` for one fixed `c`.

**Formalization Note.** The printed "(a_X r, a_Z t)" in the first sentence is read as
`(a_X r, a_Z t∗)`. Clause (2) is stated for every completion `t∗` (the proof uses only
`(a_X r, a_Z t∗) ∈ M_ψ`), which includes the paper's `t∗`. "Outputs `(a, r)`" is
`0 < Q^k_ψ(a, r)`. `M_ψ` is the published `QuantumHMMR.stabilizerLabels ψ` = `{x : W_x ψ = ±ψ}` with
`W_{(a,b)} = ⊗_i i^{a_i b_i} X^{a_i} Z^{b_i}`, which is the Hermitian Weyl operator `P_x` of p. 12. -/
theorem hiddenShift_support_affine {k m : ℕ} (ψ : EuclideanSpace ℂ (Qubits (k + m)))
    (hψ : IsStabilizerState ψ) (a : CutRankSched.Pauli k) (r : Fin m → ZMod 2) (hpos : 0 < pbds ψ (a, r)) :
    (∃ t : Fin m → ZMod 2, concat a r t ∈ QuantumHMMR.stabilizerLabels ψ) ∧
      ∀ t₀ : Fin m → ZMod 2, concat a r t₀ ∈ QuantumHMMR.stabilizerLabels ψ →
        ∃ c : ZMod 2, ∀ (s : Fin m → ZMod 2) (b : ZMod 2),
          0 < hsProb ψ a r (∑ j, t₀ j * r j) (s, b) → b = (∑ j, t₀ j * s j) + c := by sorry

end StabTestMem
