-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_11_9_4
-- name    : WildeQIT.Compression.Supplement.theorem_11_9_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:14:46.898053+00:00
-- url     : https://prove2.me/theorems/09e0693e-dc65-5115-8231-a32a3f473615
-- title:
--   Theorem 11.9.4 (Data Processing for Mutual Information): $I(A;B)_\rho\ge I(A';B')_\sigma$
-- statement:
--   Let $\rho_{AB}\in\mathcal D(\mathcal H_A\otimes\mathcal H_B)$, and let $\mathcal N:\mathcal L(\mathcal H_A)\to\mathcal L(\mathcal H_{A'})$ and $\mathcal M:\mathcal L(\mathcal H_B)\to\mathcal L(\mathcal H_{B'})$ be quantum channels. Set $\sigma_{A'B'}=(\mathcal N_{A\to A'}\otimes\mathcal M_{B\to B'})(\rho_{AB})$. Then
--
--   $$
--   I(A;B)_\rho\ge I(A';B')_\sigma,
--   $$
--
--   where $I(A;B)=H(A)+H(B)-H(AB)$ is the quantum mutual information.
--
--   Local processing cannot increase the correlations between two systems.
--
--   **Formalization Note** $\mathcal N\otimes\mathcal M$ is the published `WildeQIT.Degradable.tensorChannel`; the four systems have independent finite dimensions.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.9.4, p. 351, eq. (11.196)

import Mathlib
import Definitions.Def_WildeQIT_AFW_qMutualInfo
import Definitions.Def_WildeQIT_Degradable_tensorChannel
import Definitions.Def_WildeQIT_IsDensityOperator

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.9.4, p. 351.
-/

namespace WildeQIT.Compression.Supplement

/-- **Theorem 11.9.4 (Data Processing for Mutual Information)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 351, (11.196)): "Let
`ρ_AB ∈ D(H_A ⊗ H_B)`, `N : L(H_A) → L(H_A′)` be a quantum channel, and `M : L(H_B) → L(H_B′)` be
a quantum channel. Set `σ_A′B′ ≡ (N_{A→A′} ⊗ M_{B→B′})(ρ_AB)`. Then … `I(A;B)_ρ ≥ I(A′;B′)_σ`."

Formalization Note: `N ⊗ M` is the published `WildeQIT.Degradable.tensorChannel` (Kraus operators
`Kᵢ ⊗ Lⱼ`) acting on `a × b`; the four systems have independent finite dimensions. `I(A;B)` is
the published `WildeQIT.AFW.qMutualInfo` (bits). -/
theorem theorem_11_9_4 {a b a' b' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b']
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : IsDensityOperator ρ) (N : QChannel a a')
    (M : QChannel b b') :
    WildeQIT.AFW.qMutualInfo ((WildeQIT.Degradable.tensorChannel N M).apply ρ) ≤
      WildeQIT.AFW.qMutualInfo ρ := by sorry

end WildeQIT.Compression.Supplement
