-- Prove2me | Theorems.Thm_WildeQIT_EntManip_theorem_19_2_1
-- name    : WildeQIT.EntManip.theorem_19_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:38:23.950932+00:00
-- url     : https://prove2.me/theorems/064f5d84-fb10-438f-adea-24f3f4a0b39b
-- title:
--   Theorem 19.2.1: the relative entropy of entanglement is an LOCC monotone
-- statement:
--   Let $\Lambda_{AB\to A'B'}$ be an LOCC channel between finite-dimensional bipartite systems (a finite composition of one-way rounds $\sum_x\mathcal F^x_A\otimes\mathcal G^x_B$ and their $B\to A$ counterparts, §19.2), and let $\rho_{AB}\in\mathcal D(\mathcal H_A\otimes\mathcal H_B)$. Then
--
--   $$
--   E_R(A;B)_\rho\ \ge\ E_R(A';B')_{\Lambda(\rho)} .
--   $$
--
--   That is, the relative entropy of entanglement is non-increasing under LOCC. In the converse of the entanglement manipulation theorem this is the step that relates the input entanglement to the output entanglement.
--
--   **Formalization Note** Both sides are extended reals (`EReal`), the relative entropy of entanglement being an infimum of relative entropies over separable states.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces H_A, H_B → complex matrices over finite index types a, b; reason: the book's standing setting; same instances
--   - encoding: min over separable states → infimum in EReal; reason: the infimum is attained in finite dimensions; same value
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 19.2.1, (19.26), p. 539

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_EntManip_IsLOCC
import Definitions.Def_WildeQIT_EntManip_relEntEntanglement

namespace WildeQIT.EntManip

/-- **Theorem 19.2.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 539): "The relative entropy of entanglement is an LOCC monotone", i.e. it is non-increasing
under every LOCC channel (§19.2, p. 538): for every LOCC channel `Λ_{AB→A'B'}` and every state
`ρ_AB`, `E_R(A;B)_ρ ≥ E_R(A';B')_{Λ(ρ)}` (19.26).

**Formalization Note** Finite-dimensional systems indexed by finite types; `IsLOCC` is §19.2's
class of finite compositions of one-way rounds (19.21); `E_R` takes values in `EReal`
(Definition 19.2.1). -/
theorem theorem_19_2_1 {a b a' b' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b']
    (Λ : Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ) (hΛ : IsLOCC Λ)
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    relEntEntanglement (Λ ρ) ≤ relEntEntanglement ρ := by sorry

end WildeQIT.EntManip
