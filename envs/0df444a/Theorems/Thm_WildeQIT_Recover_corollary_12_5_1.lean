-- Prove2me | Theorems.Thm_WildeQIT_Recover_corollary_12_5_1
-- name    : WildeQIT.Recover.corollary_12_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:22:16.570372+00:00
-- url     : https://prove2.me/theorems/64333f1d-b4a2-4aa5-af8f-20cac637f7ea
-- title:
--   Corollary 12.5.1 (Equality Conditions) — $D(\rho\|\sigma)=D(\mathcal N(\rho)\|\mathcal N(\sigma))$ iff every rotated Petz map recovers $\rho$
-- statement:
--   Let $\rho$ be a density operator and $\sigma$ a positive semi-definite operator on a finite-dimensional Hilbert space $\mathcal H$ with $\operatorname{supp}(\rho)\subseteq\operatorname{supp}(\sigma)$, and let $\mathcal N:\mathcal L(\mathcal H)\to\mathcal L(\mathcal H')$ be a quantum channel. Then
--
--   $$
--   D(\rho\|\sigma)=D(\mathcal N(\rho)\|\mathcal N(\sigma))
--   \quad\Longleftrightarrow\quad
--   \forall t\in\mathbb R:\ (\mathcal R^t_{\sigma,\mathcal N}\circ\mathcal N)(\rho)=\rho .
--   $$
--
--   This is the characterization of the equality case in the monotonicity of quantum relative entropy: the relative entropy is preserved exactly when the rotated Petz maps, which always restore $\sigma$, also restore $\rho$.
--
--   **Formalization Note** Relative entropies are extended reals in bits; the channel is given in Choi–Kraus form.
--
--   Differences from the source:
--   - encoding: a quantum channel → a channel in Choi–Kraus form; reason: every channel has a finite Kraus form (Theorem 4.4.1).
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 12.5.1, (12.116)–(12.117), p. 380

import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_Recover_qRelEntropy
import Definitions.Def_WildeQIT_Recover_rotatedPetz
open scoped ComplexOrder

namespace WildeQIT.Recover

/-- **Corollary 12.5.1 (Equality Conditions)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Corollary 12.5.1, (12.116)–(12.117), p. 380). For `ρ`, `σ`, `𝒩` as in
Definition 12.1.1, `D(ρ‖σ) = D(𝒩(ρ)‖𝒩(σ))` if and only if every rotated Petz map recovers `ρ`
from `𝒩(ρ)`: `(ℛ^t_{σ,𝒩} ∘ 𝒩)(ρ) = ρ` for all `t ∈ ℝ`.

**Formalization Note** Finite dimensions; `log` base 2; relative entropies in `EReal`. -/
theorem corollary_12_5_1 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    qRelEntropy ρ σ = qRelEntropy (N.apply ρ) (N.apply σ) ↔
      ∀ t : ℝ, rotatedPetz σ N t (N.apply ρ) = ρ := by sorry

end WildeQIT.Recover
