-- Prove2me | Theorems.Thm_ShendeQSD_Synthesis_demux_rot
-- name    : ShendeQSD.Synthesis.demux_rot
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:31.108996+00:00
-- url     : https://prove2.me/theorems/cd3c4ad6-c267-467d-a824-085f1c22008a
-- title:
--   Theorem 8: demultiplexing multiplexed $R_k$ gates, $k=y,z$
-- statement:
--   Let $R$ be $R_z$ or $R_y$. Consider a target qubit, an extra select qubit $s_0$, and a finite select register $\sigma$ (the bus). Let $C$ be the CNOT with control $s_0$ and target the target qubit. For angles $\varphi$ of the bus alone, $\mathcal R(\varphi)$ denotes the multiplexed $R$ with selects the bus (it ignores $s_0$).
--
--   1. Every multiplexed $R$ gate $\mathcal R(\theta)$ with selects $(s_0,\text{bus})$ equals $C\,\mathcal R(\theta'')\,C\,\mathcal R(\theta')$ for some bus angles $\theta',\theta''$.
--   2. Conversely, every product $C\,\mathcal R(\theta'')\,C\,\mathcal R(\theta')$ is a multiplexed $R$ with selects $(s_0,\text{bus})$.
--   3. The order may be reversed: every $\mathcal R(\theta)$ equals $\mathcal R(\theta')\,C\,\mathcal R(\theta'')\,C$ for some bus angles.
--   4. Conversely, every product of the reversed shape is a multiplexed $R$.
--
--   Applied recursively, this decomposes a multiplexed rotation with $k$ selects into one-qubit rotations and CNOTs.
--
--   **Formalization Note** The index is `Bool × (Bool × σ)` = (target, ($s_0$, bus)); $C$ is `cnotFromSelect`, $\mathcal R(\varphi)$ is `muxRot R (φ ∘ Prod.snd)`. $R_y$ is the paper's.
--
--   Differences from the source:
--   - encoding: the target qubit drawn at the bottom → the target as the first tensor factor; reason: the same operator up to the order of the tensor factors
--   - reading: the circuit equivalence ≅ (p. 7) and the remark that the order may be reversed → both directions of ≅, for the printed order and for the reversed order; reason: the paper's definition of ≅ for generic gates quantifies over both sides, and the reversal remark on p. 11 is part of the result used in Figure 2
--   - generalization: the bus is a register of qubits (the slashed wire, k − 1 select qubits) → any finite type σ; reason: specializes to σ = Qubits (k − 1), and the identity holds blockwise in the bus for any index type
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, Theorem 8 and the remark after it, p. 11

import Definitions.Def_ShendeQSD_Synthesis_muxRot
import Definitions.Def_ShendeQSD_Synthesis_cnotFromSelect
import Definitions.Def_ShendeQSD_Synthesis_rz
import Definitions.Def_ShendeQSD_Synthesis_ry

namespace ShendeQSD.Synthesis

/-- **Theorem 8: demultiplexing multiplexed `R_k` gates, `k = y, z`.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
Theorem 8, p. 11: a multiplexed `R_k` whose selects are a top qubit `s₀` and a bus equals, read
left to right, a multiplexed `R_k` with the bus as selects, a CNOT from `s₀` to the target, a
multiplexed `R_k` with the bus as selects, a CNOT from `s₀` to the target. "It is worth noting
that since every gate appearing in Theorem 8 is symmetric, the order of gates in this
decomposition may be reversed."

For `R = R_z` and `R = R_y`, on the index (target, (`s₀`, bus `σ`)), with `C` = `cnotFromSelect`:
1. every `muxRot R θ` equals `C · muxRot R (θ'' ∘ snd) · C · muxRot R (θ' ∘ snd)` for some
   angles `θ', θ''` of the bus alone;
2. conversely, every such product is a multiplexed `R` with selects (`s₀`, bus);
3. reversed order: every `muxRot R θ` equals `muxRot R (θ' ∘ snd) · C · muxRot R (θ'' ∘ snd) · C`;
4. conversely, every product of the reversed shape is a multiplexed `R`.

**Formalization Note.** Generalization: the bus is any finite type `σ` (the paper's is a register
of qubits, `σ = Qubits (k-1)`). Encoding: the target is the first factor (`muxRot`'s orientation); the
paper draws it at the bottom. `θ' ∘ Prod.snd` is a multiplexed rotation that ignores `s₀`. The
matrix product is the diagram read right to left. -/
theorem demux_rot {σ : Type*} [Fintype σ] [DecidableEq σ] (R : ℝ → Matrix Bool Bool ℂ)
    (hR : R = rz ∨ R = ry) :
    (∀ θ : Bool × σ → ℝ, ∃ θ' θ'' : σ → ℝ,
      muxRot R θ = cnotFromSelect (σ := σ) * muxRot R (θ'' ∘ Prod.snd) *
        cnotFromSelect (σ := σ) * muxRot R (θ' ∘ Prod.snd)) ∧
    (∀ θ' θ'' : σ → ℝ, ∃ θ : Bool × σ → ℝ,
      cnotFromSelect (σ := σ) * muxRot R (θ'' ∘ Prod.snd) *
        cnotFromSelect (σ := σ) * muxRot R (θ' ∘ Prod.snd) = muxRot R θ) ∧
    (∀ θ : Bool × σ → ℝ, ∃ θ' θ'' : σ → ℝ,
      muxRot R θ = muxRot R (θ' ∘ Prod.snd) * cnotFromSelect (σ := σ) *
        muxRot R (θ'' ∘ Prod.snd) * cnotFromSelect (σ := σ)) ∧
    (∀ θ' θ'' : σ → ℝ, ∃ θ : Bool × σ → ℝ,
      muxRot R (θ' ∘ Prod.snd) * cnotFromSelect (σ := σ) *
        muxRot R (θ'' ∘ Prod.snd) * cnotFromSelect (σ := σ) = muxRot R θ) := by sorry

end ShendeQSD.Synthesis
