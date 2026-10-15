-- Prove2me | Theorems.Thm_QuantumSDP18_MeasureBE_povm_block_encoding
-- name    : QuantumSDP18.MeasureBE.povm_block_encoding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:23.050639+00:00
-- url     : https://prove2.me/theorems/15991233-ec18-44ab-87a5-36cdee8ed74e
-- title:
--   §4.1, p. 25 — an ε-biased implementation of a two-outcome POVM {M, I − M} gives the (1, a + 1, ε)-block-encoding U′†(I ⊗ CNOT)U′ of M
-- statement:
--   Let $\{M, I-M\}$ be a two-outcome POVM on a finite-dimensional system, so $M$ and $I - M$ are positive semidefinite. Suppose the measurement is implemented on a quantum computer as follows: attach $a$ ancilla qubits in $|0\rangle^{\otimes a}$, apply a unitary $U$, and accept when the last ancilla qubit reads $|0\rangle$. Suppose that this implementation has **bias at most** $\varepsilon\ge 0$, that is, for every density matrix $\rho$ on the system,
--
--   $$
--   \Big|\operatorname{Tr}\Big((I\otimes|0\rangle\langle 0|)\,U\big(\rho\otimes|0\rangle\langle 0|^{\otimes a}\big)U^\dagger\Big) - \operatorname{Tr}(M\rho)\Big| \le \varepsilon. \tag{14}
--   $$
--
--   Let $a' = a + 1$, $U' = U\otimes I_2$ (one fresh qubit), and let $\mathrm{CNOT}$ be controlled by the measured qubit and target the fresh qubit. Then
--
--   $$
--   U'^\dagger(I\otimes\mathrm{CNOT})U' \text{ is a } (1, a', \varepsilon)\text{-block-encoding of } M,
--   $$
--
--   that is, it is unitary and $\big\|M - (\langle 0|^{\otimes a'}\otimes I)\,U'^\dagger(I\otimes\mathrm{CNOT})U'\,(|0\rangle^{\otimes a'}\otimes I)\big\| \le \varepsilon$ in the operator norm (Definition 2).
--
--   The result says that any reasonable implementation of a measurement yields, at essentially no extra cost, the block-encoding of its POVM element that the paper's quantum operator input model takes as input.
--
--   **Formalization Note** The system is an arbitrary finite type; $a = c + 1 \ge 1$ ancillas, the last of which is measured. The block-encoding predicate is the platform's `QAlgorithms.IsBlockEncoding`, which takes the ancilla register first, as Definition 2 does; the circuit (written system-first, as on p. 25) is reindexed accordingly, and the all-zero element of the $a'$ ancillas is $(|0\rangle^{\otimes a}, 0)$. The hypothesis $\varepsilon \ge 0$ is added; it matters only for a zero-dimensional system, where (14) is vacuous. (14) ranges over all density matrices, as the page's "$\forall\rho$" over mixed states does.
-- source:
--   van Apeldoorn and Gilyén, Improvements in quantum SDP-solving with applications, arXiv:1804.05058v1, p. 25, §4.1, 'therefore U′†(I ⊗ CNOT)U′ is a (1, a′, ε)-block-encoding of M' (setting pp. 24–25, (14); Definition 2, p. 4)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_MeasureBE_Setting

namespace QuantumSDP18.MeasureBE

open scoped ComplexOrder

/-- §4.1, p. 25: if a two-outcome POVM `{M, I − M}` is implemented by attaching `a` ancilla
qubits in `|0⟩`, applying a unitary `U` and accepting when the last qubit reads `0`, with bias at
most `ε` (equation (14)), then `U′† (I ⊗ CNOT) U′` with `U′ = U ⊗ I₂` is a
`(1, a + 1, ε)`-block-encoding of `M` (Definition 2, p. 4; ancilla register moved first). -/
theorem povm_block_encoding {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℕ)
    (U : Matrix (ι × Anc c) (ι × Anc c) ℂ) (M : Matrix ι ι ℂ) (ε : ℝ)
    (hU : U ∈ Matrix.unitaryGroup (ι × Anc c) ℂ) (hM : M.PosSemidef) (hIM : (1 - M).PosSemidef)
    (hε : 0 ≤ ε)
    (h14 : ∀ ρ : Matrix ι ι ℂ, IsDensity ρ → ‖accProb c U ρ - (M * ρ).trace‖ ≤ ε) :
    QAlgorithms.IsBlockEncoding ((ancZero c, false) : Anc c × Bool)
      (Matrix.reindex (reorder c) (reorder c)
        ((Uprime c U).conjTranspose * cnotLast (ι := ι) c * Uprime c U)) 1 ε M := by sorry

end QuantumSDP18.MeasureBE
