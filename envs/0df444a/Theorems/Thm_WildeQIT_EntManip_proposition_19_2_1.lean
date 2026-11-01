-- Prove2me | Theorems.Thm_WildeQIT_EntManip_proposition_19_2_1
-- name    : WildeQIT.EntManip.proposition_19_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:37:21.780488+00:00
-- url     : https://prove2.me/theorems/75070c31-1d04-4739-91a6-5c9fceab0488
-- title:
--   Proposition 19.2.1: $E_R(A;B)_\rho\ge\max\{I(A\rangle B)_\rho,I(B\rangle A)_\rho\}$
-- statement:
--   Let $\rho_{AB}\in\mathcal D(\mathcal H_A\otimes\mathcal H_B)$ be a state of finite-dimensional systems. Then the relative entropy of entanglement is never smaller than the coherent information in either direction:
--
--   $$
--   E_R(A;B)_\rho\ \ge\ \max\{I(A\rangle B)_\rho,\ I(B\rangle A)_\rho\},
--   $$
--
--   where $I(A\rangle B)_\rho=H(B)_\rho-H(AB)_\rho$ and $I(B\rangle A)_\rho=H(A)_\rho-H(AB)_\rho$.
--
--   This lower bound converts the relative entropy of entanglement of the output of an LOCC protocol into an entropic quantity that is continuous in the state.
--
--   **Formalization Note** The coherent informations are real numbers in bits, cast into the extended reals in which $E_R$ is valued.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces H_A, H_B → complex matrices over finite index types a, b; reason: the book's standing setting; same instances
--   - encoding: min over separable states → infimum in EReal; reason: the infimum is attained in finite dimensions; same value
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Proposition 19.2.1, (19.27), p. 539

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_EntManip_coherentInfoAB
import Definitions.Def_WildeQIT_EntManip_coherentInfoBA
import Definitions.Def_WildeQIT_EntManip_relEntEntanglement

namespace WildeQIT.EntManip

/-- **Proposition 19.2.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 539): "Let `ρ_AB ∈ D(H_A ⊗ H_B)`. Then the relative entropy of entanglement is never smaller
than the coherent information: `E_R(A; B)_ρ ≥ max{I(A⟩B)_ρ, I(B⟩A)_ρ}`." (19.27)

**Formalization Note** `I(A⟩B)_ρ = H(B) − H(AB)` and `I(B⟩A)_ρ = H(A) − H(AB)` are real numbers
(bits), cast into `EReal`, where `E_R` lives. -/
theorem proposition_19_2_1 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    ((max (coherentInfoAB ρ) (coherentInfoBA ρ) : ℝ) : EReal) ≤ relEntEntanglement ρ := by sorry

end WildeQIT.EntManip
