-- Prove2me | Theorems.Thm_WildeQIT_AFW_condMutualInfo_recovery_bound
-- name    : WildeQIT.AFW.condMutualInfo_recovery_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:38:06.242578+00:00
-- url     : https://prove2.me/theorems/970a76be-81a4-45d1-811a-a88297981fce
-- title:
--   Theorem 11.10.5: $I(A;B|C)_\rho,\ I(A;B|C)_\sigma \le 2\Delta\log\dim\mathcal H_B + g_2(\Delta)$ with $\Delta$ the recovery distance
-- statement:
--   Let $\rho_{ABC}$ be a density operator on $\mathcal H_A\otimes\mathcal H_B\otimes\mathcal H_C$ with marginal $\rho_{BC}$, and let
--
--   $$
--   \Delta \equiv \tfrac12 \inf_{\mathcal R_{C\to AC}} \bigl\|\rho_{ABC} - \mathcal R_{C\to AC}(\rho_{BC})\bigr\|_1 ,
--   $$
--
--   the infimum over quantum channels $\mathcal R: \mathcal L(\mathcal H_C)\to\mathcal L(\mathcal H_A\otimes\mathcal H_C)$. Write $I(A;B|C)$ for the conditional quantum mutual information (base-2 logarithms) and $g_2(\Delta) = (\Delta+1)\log_2(\Delta+1) - \Delta\log_2\Delta$. Then
--
--   1. $$I(A;B|C)_\rho \le 2\Delta\log\dim(\mathcal H_B) + g_2(\Delta) ;$$
--   2. for every channel $\mathcal R^*_{C\to AC}$ attaining the infimum, i.e. with $\tfrac12\|\rho_{ABC} - \mathcal R^*_{C\to AC}(\rho_{BC})\|_1 = \Delta$, the recovered state $\sigma_{ABC} \equiv \mathcal R^*_{C\to AC}(\rho_{BC})$ satisfies
--   $$I(A;B|C)_\sigma \le 2\Delta\log\dim(\mathcal H_B) + g_2(\Delta) .$$
--
--   This is a quantitative converse to the statement that conditional mutual information vanishes on quantum Markov chains: if $\rho_{ABC}$ can be nearly recovered from $\rho_{BC}$ by acting on $C$ alone, then $I(A;B|C)_\rho$ is small.
--
--   **Formalization Note** The tripartite space is `A × (B × C)`; $\rho_{BC}$ is `WildeQIT.partialTraceLeft ρ`; channels are published `WildeQIT.QChannel C (A × C)` (Choi–Kraus form); $\mathcal R(\rho_{BC})$ is `WildeQIT.AFW.recoverBC`; $\Delta$ is `WildeQIT.AFW.recoveryDist ρ`; $I(A;B|C)$ is `WildeQIT.AFW.qCondMutualInfo`.
--
--   Differences from the source:
--   - reading: "$\mathcal R^*_{C\to AC}$ the optimal recovery channel in (11.283)" → every channel $\mathcal R^*$ with $\tfrac12\|\rho_{ABC} - \mathcal R^*(\rho_{BC})\|_1 = \Delta$; reason: "optimal" means attaining the infimum, and the book's statement is for the optimizer whatever it is; an optimizer exists by compactness of the set of channels, so the clause is not vacuous.
--   - encoding: channels $\mathcal R: \mathcal L(\mathcal H_C)\to\mathcal L(\mathcal H_A\otimes\mathcal H_C)$ → `WildeQIT.QChannel C (A × C)` in Choi–Kraus form; reason: by Theorem 4.4.1 every channel has a finite Kraus decomposition, so the infimum ranges over the same maps.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.10.5, (11.283)–(11.284), p. 362

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_AFW_g2
import Definitions.Def_WildeQIT_AFW_qCondMutualInfo
import Definitions.Def_WildeQIT_AFW_recoverBC
import Definitions.Def_WildeQIT_AFW_recoveryDist

namespace WildeQIT.AFW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.10.5, p. 362:
"Let ρ_ABC ∈ D(H_A ⊗ H_B ⊗ H_C) and let ∆ ≡ ½ inf_{R_{C→AC}} ∥ρ_ABC − R_{C→AC}(ρ_BC)∥₁, (11.283)
where the optimization is with respect to channels R : L(H_C) → L(H_A ⊗ H_C). Then
I(A; B|C)_ρ, I(A; B|C)_σ ≤ 2∆ log dim(H_B) + g₂(∆), (11.284)
where σ_ABC ≡ R*_{C→AC}(ρ_BC) with R*_{C→AC} the optimal recovery channel in (11.283)."

The first conjunct is the bound for `ρ`; the second is the bound for `σ = R*(ρ_BC)`, for every
channel `R*` attaining the infimum in (11.283).

**Formalization Note.** `H_A ⊗ H_B ⊗ H_C` is the index type `A × (B × C)`; `ρ_BC = Tr_A ρ` is
`WildeQIT.partialTraceLeft ρ`; channels are published `WildeQIT.QChannel C (A × C)` (Choi–Kraus
form); `R(ρ_BC)` is `WildeQIT.AFW.recoverBC R ρ_BC`; `∆` is `WildeQIT.AFW.recoveryDist ρ`;
`I(A; B|C)` is `WildeQIT.AFW.qCondMutualInfo`; `log` is `log₂`. "The optimal recovery channel" is
read as any channel whose value `½∥ρ − R*(ρ_BC)∥₁` equals `∆`. -/
theorem condMutualInfo_recovery_bound {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C] (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) :
    qCondMutualInfo ρ ≤
        2 * recoveryDist ρ * Real.logb 2 (Fintype.card B) + g2 (recoveryDist ρ) ∧
    ∀ Rstar : WildeQIT.QChannel C (A × C),
      WildeQIT.traceNorm (ρ - recoverBC Rstar (WildeQIT.partialTraceLeft ρ)) / 2 = recoveryDist ρ →
      qCondMutualInfo (recoverBC Rstar (WildeQIT.partialTraceLeft ρ)) ≤
        2 * recoveryDist ρ * Real.logb 2 (Fintype.card B) + g2 (recoveryDist ρ) := by sorry

end WildeQIT.AFW
