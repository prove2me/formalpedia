-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_11_8_1
-- name    : WildeQIT.Compression.Supplement.theorem_11_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:13:38.903918+00:00
-- url     : https://prove2.me/theorems/2eca658b-5224-4633-990b-0c09a96f9b4f
-- title:
--   Theorem 11.8.1 (Monotonicity of Quantum Relative Entropy): $D(\rho\|\sigma)\ge D(\mathcal N(\rho)\|\mathcal N(\sigma))$
-- statement:
--   Let $\rho\in\mathcal D(\mathcal H)$ be a density operator, $\sigma\in\mathcal L(\mathcal H)$ positive semidefinite, and $\mathcal N:\mathcal L(\mathcal H)\to\mathcal L(\mathcal H')$ a quantum channel. Then the quantum relative entropy can only decrease under the channel:
--
--   $$
--   D(\rho\|\sigma)\ge D(\mathcal N(\rho)\|\mathcal N(\sigma)),
--   $$
--
--   where $D(\rho\|\sigma)=\operatorname{Tr}\{\rho[\log\rho-\log\sigma]\}$ if $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$ and $D(\rho\|\sigma)=+\infty$ otherwise.
--
--   This data-processing inequality is the source of most entropy inequalities of quantum Shannon theory.
--
--   **Formalization Note** $D$ is the published `WildeQIT.QMemory.qRelEntropy`, valued in the extended reals; $\sigma$ need not be normalized, and the channel may change the dimension.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.8.1, p. 342, eq. (11.118)

import Mathlib
import Definitions.Def_WildeQIT_QMemory_qRelEntropy
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_IsDensityOperator

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.8.1, p. 342.
-/

open scoped ComplexOrder

namespace WildeQIT.Compression.Supplement

/-- **Theorem 11.8.1 (Monotonicity of Quantum Relative Entropy)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 342, (11.118)):
"Let `ρ ∈ D(H)`, `σ ∈ L(H)` be positive semi-definite, and `N : L(H) → L(H′)` be a quantum
channel. … `D(ρ‖σ) ≥ D(N(ρ)‖N(σ))`."

Formalization Note: `D` is the published `WildeQIT.QMemory.qRelEntropy` (`EReal`-valued, `+∞`
off support, Definition 11.8.2), the channel the published Kraus form `WildeQIT.QChannel`;
`H` and `H′` are indexed by independent finite types, so the channel may change dimension. -/
theorem theorem_11_8_1 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ σ : Matrix a a ℂ) (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (N : QChannel a b) :
    WildeQIT.QMemory.qRelEntropy (N.apply ρ) (N.apply σ) ≤ WildeQIT.QMemory.qRelEntropy ρ σ := by sorry

end WildeQIT.Compression.Supplement
