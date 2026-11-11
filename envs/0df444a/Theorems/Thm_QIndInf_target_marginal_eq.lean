-- Prove2me | Theorems.Thm_QIndInf_target_marginal_eq
-- name    : QIndInf.target_marginal_eq
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:28:48.016212+00:00
-- url     : https://prove2.me/theorems/eb1d86cf-f6d5-47a7-93a0-a48e67403b45
-- title:
--   Eq. (65) — the target's marginal on the past registers is the learner's input
-- statement:
--   Let $\rho$ be a quantum source, $\mathcal I_1,\dots,\mathcal I_i$ instruments and $h_{<i}$ a history with outcomes $x_1,\dots,x_{i-1}$. Discarding the next register and its outcome from the prediction target gives the learner's input:
--
--   $$
--   \mathcal N_i\big(\tau_{\le i|h<i}\big)=\mathrm{Tr}_{R_iX_i}\,\tau_{\le i|h<i}=\rho_{<i|h<i}.
--   $$
--
--   This is the first identity of Eq. (65) (stated on p.19 as "Its marginal on $(R_1,\dots,R_{i-1})$ is exactly the learner's input state"). It is what lets the recovery inequality, applied to the channel $\mathcal N_i$, compare the learner's output with the target.
--
--   Differences from the source:
--   - generalization: ρ_{R1…Rm} ∈ C_{n,m}[s,t] → any quantum source (consistent family of density operators); reason: the identity uses only consistency of the source and trace preservation of the instrument; the paper's sources are consistent sources
--   - encoding: registers R_i of n qubits; outcome register written first in M_I → Fin (2^n) per register, register R_i = coordinate i−1; output indexed (past registers) × (next register × outcome); reason: relabelling of the index set; changes no trace, trace distance or relative entropy
--   - encoding: conditional states defined for histories of positive probability → 0⁻¹ = 0 makes them the zero matrix on histories of probability zero; reason: those histories have weight zero in every sum; only undefined cases are affected
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), §4.1, p.19 (after Eq. (55)); §4.2, Eq. (65), p.21

import Mathlib
import Definitions.Def_QIndInf_target
import Definitions.Def_WildeQIT_partialTrace

set_option autoImplicit false

namespace QIndInf

open QAlgorithms.CopyMeasurements

/-- **The target's marginal on the past registers is the learner's input** (p.19 after
Eq. (55); first identity of Eq. (65)). For every quantum source `ρ`, every round with `j` past
registers, all instruments `I₁, …, I_{j+1}` and every history `x`,
`N_i(τ_{≤i|h<i}) = Tr_{R_i X_i} τ_{≤i|h<i} = ρ_{<i|h<i}`.

arXiv:2609.36912 (PDF of 2026-11-02), §4.1, p.19 ("Its marginal on (R₁, ..., R_{i−1}) is exactly
the learner's input state ρ_{<i|h<i}") and §4.2, Eq. (65), p.21.

**Formalization Note.** `N_i` is `WildeQIT.partialTraceRight` over the factor `R_i × X_i`.
Round `i` has `j = i − 1` past registers. On a history of probability zero both sides are the zero
matrix. -/
theorem target_marginal_eq {n j : ℕ} (ρ : QuantumProcess n) {k : Fin (j + 1) → ℕ}
    (I : (l : Fin (j + 1)) → QuantumInstrument (Reg n) (Fin (k l)))
    (x : (l : Fin j) → Fin (k l.castSucc)) :
    WildeQIT.partialTraceRight (target ρ.state I x) = condPast ρ.state (pastInstr I) x := by sorry

end QIndInf
