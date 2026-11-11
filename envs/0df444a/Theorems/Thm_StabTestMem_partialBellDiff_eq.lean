-- Prove2me | Theorems.Thm_StabTestMem_partialBellDiff_eq
-- name    : StabTestMem.partialBellDiff_eq
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:10.606898+00:00
-- url     : https://prove2.me/theorems/cc7aa9df-210c-47e8-b6c1-5b5090dc5bd4
-- title:
--   Lemma 4.2 — law of partial Bell difference sampling
-- statement:
--   Let $|\psi\rangle$ be a pure state on $n=k+m$ qubits and let $Q^k_\psi$ be the output distribution of partial Bell difference sampling with $k$ qubits of memory (Algorithm 2). Then for every $(a,r)\in\mathbb F_2^{2k}\times\mathbb F_2^m$,
--
--   $$Q^k_\psi(a,r)=\sum_{t\in\mathbb F_2^m}(p_\psi\star p_\psi)(a_Xr,\,a_Zt),$$
--
--   where $p_\psi$ is the characteristic distribution and $\star$ the convolution on $\mathbb F_2^{2n}$.
--
--   The partial sampler thus sees the Bell difference law $p_\psi\star p_\psi$ marginalized over the Z-part of the last $m$ qubits. For a stabilizer state it gives the fraction of stabilizers with prefix $(a,r)$.
--
--   Differences from the source:
--   - encoding: n qubits with m = n − k → k + m qubits; reason: the same instances; the paper's m := n − k
--   - encoding: Q^k_ψ: the output distribution of Algorithm 2 → two independent runs of the POVM of Eq. (25) on pairs of copies, outcomes added (pbds); reason: this is how Algorithm 2 produces its output
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 4.2, p. 24 (= Corollary 3.3, p. 18)

import Definitions.Def_StabTestMem_pbds
import Definitions.Def_StabTestMem_charDist
import Definitions.Def_StabTestMem_conv
import Definitions.Def_StabTestMem_concat

namespace StabTestMem

open QAlgorithms

/-- **Lemma 4.2 (= Corollary 3.3): the law of partial Bell difference sampling.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 4.2,
p. 24: "Let Q^k_ψ be the output distribution of Algorithm 2. Then, for every
(a, r) ∈ F_2^{2k} × F_2^m, Q^k_ψ(a, r) = Σ_{t∈F_2^m} (p_ψ ⋆ p_ψ)(a_X r, a_Z t)."

For a pure state `ψ` on `k + m` qubits, the probability that Algorithm 2 (two independent runs of
partial Bell sampling, outcomes added) returns `(a, r)` equals `Σ_t (p_ψ ⋆ p_ψ)(a_X r, a_Z t)`.

**Formalization Note.** `n = k + m` (the paper's `m = n − k`). `pbds` is built from the POVM of
Eq. (25), not from this formula. -/
theorem partialBellDiff_eq {k m : ℕ} (ψ : EuclideanSpace ℂ (Qubits (k + m))) (hψ : IsState ψ)
    (a : CutRankSched.Pauli k) (r : Fin m → ZMod 2) :
    pbds ψ (a, r) = ∑ t : Fin m → ZMod 2, conv (charDist ψ) (charDist ψ) (concat a r t) := by sorry

end StabTestMem
