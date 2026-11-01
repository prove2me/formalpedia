-- Prove2me | Theorems.Thm_WildeQIT_QMemory_proposition_11_8_1
-- name    : WildeQIT.QMemory.proposition_11_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:09.710872+00:00
-- url     : https://prove2.me/theorems/de320064-83fa-4968-b8ee-d8baf8a15eaf
-- title:
--   Proposition 11.8.1 — $D(\rho\|\sigma)=\lim_{\varepsilon\searrow 0}D(\rho\|\sigma+\varepsilon I)$
-- statement:
--   Let $\rho$ be a density operator and $\sigma$ a positive semi-definite operator on a finite-dimensional Hilbert space. Then
--
--   $$
--   D(\rho\|\sigma)=\lim_{\varepsilon\searrow 0}D(\rho\|\sigma+\varepsilon I).
--   $$
--
--   In particular the limit is $+\infty$ exactly when $\operatorname{supp}(\rho)\not\subseteq\operatorname{supp}(\sigma)$; this justifies the support convention in the definition of the relative entropy.
--
--   **Formalization Note** The limit is taken in the extended reals along $\varepsilon\to 0^+$.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces and their tensor products → complex matrices indexed by finite types, $\mathcal H_A\otimes\mathcal H_B$ indexed by `A × B` (Kronecker convention); reason: the book works in finite dimensions throughout; same objects.
--   - encoding: lim_{ε↘0} of extended-real values → `Tendsto` along `𝓝[>] 0` in `EReal`; reason: Lean's notion of a one-sided limit; +∞ is a limit point of `EReal`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Proposition 11.8.1, eq. (11.109), p. 341

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QMemory_qRelEntropy

open Filter Topology
open scoped ComplexOrder

namespace WildeQIT.QMemory

/-- **Proposition 11.8.1** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 341). For `ρ ∈ D(H)` and positive semi-definite `σ`,
`D(ρ‖σ) = lim_{ε↘0} D(ρ‖σ + εI)` (11.109).

**Formalization Note** The limit is taken in `EReal` along `ε → 0⁺` (`𝓝[>] 0`), so a support
violation gives the limit `+∞`, as in the book's proof. -/
theorem proposition_11_8_1 {H : Type} [Fintype H] [DecidableEq H]
    (ρ σ : Matrix H H ℂ) (hρ : WildeQIT.IsDensityOperator ρ) (hσ : σ.PosSemidef) :
    Tendsto (fun ε : ℝ => qRelEntropy ρ (σ + (ε : ℂ) • (1 : Matrix H H ℂ))) (𝓝[>] 0)
      (𝓝 (qRelEntropy ρ σ)) := by sorry

end WildeQIT.QMemory
