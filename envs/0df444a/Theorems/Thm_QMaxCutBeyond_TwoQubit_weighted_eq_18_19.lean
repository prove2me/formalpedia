-- Prove2me | Theorems.Thm_QMaxCutBeyond_TwoQubit_weighted_eq_18_19
-- name    : QMaxCutBeyond.TwoQubit.weighted_eq_18_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:16.794008+00:00
-- url     : https://prove2.me/theorems/630c2e54-4b86-4796-bdd5-262772a93fb5
-- title:
--   Weighted form of Eqs. (18)–(19) — OPT(G) ≤ W/2 + 3λ^Z_max(G), attained-by-a-basis-state lower bound W/2 + λ^Z_max(G)
-- statement:
--   Let $G=(V,E,w)$ have nonnegative weights, $W=\sum_e w_e$, $H_Z(G)=-\frac12\sum_{\{i,j\}\in E}w_{ij}Z_iZ_j$ and $\lambda^Z_{\max}(G)$ its largest eigenvalue. There is a computational basis state $|z\rangle$ such that
--
--   1. $|z\rangle$ attains $\lambda^Z_{\max}(G)$: $\langle\psi|H_Z(G)|\psi\rangle\le\langle z|H_Z(G)|z\rangle=\lambda^Z_{\max}(G)$ for every unit $\psi$;
--   2. (eq. (18)) every unit state $\psi$ satisfies
--   $$\langle\psi|H_G|\psi\rangle\;\le\;\frac W2+3\lambda^Z_{\max}(G);$$
--   3. (eq. (19)) $\langle z|H_G|z\rangle=\frac W2+\lambda^Z_{\max}(G)$, so the best product state has energy at least $\frac W2+\lambda^Z_{\max}(G)$.
--
--   Combining (18) and (19) yields a basis state of energy at least $\mathrm{OPT}(G)/3+W/3$, the first ingredient of eq. (24).
--
--   **Formalization Note** The paper writes (17)–(19) for unit weights ($|E|$ in place of $W$) and the proof of Theorem 3 reuses them weighted; this item is that weighted form. $\mathrm{PROD}(G)$ is not defined: (19) is stated through its basis-state witness $|z\rangle$, which is a product state.
-- source:
--   Anshu, Gosset & Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394v1, p. 8, eqs. (17)–(19), proof of Theorem 5 (weighted form, as used in the proof of Theorem 3, p. 9)

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace QMaxCutBeyond.TwoQubit

/-- Weighted form of Eqs. (18)–(19), p. 8: there is a computational basis state `|z⟩` attaining
`λ^Z_max(G)` (the largest energy of `H_Z(G)`), every unit state satisfies
`⟨ψ|H_G|ψ⟩ ≤ W/2 + 3 λ^Z_max(G)` (18), and `⟨z|H_G|z⟩ = W/2 + λ^Z_max(G)` (the basis-state
witness of (19)). -/
theorem weighted_eq_18_19 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e) :
    ∃ z : Config n,
      (∀ ψ : Config n → ℂ, IsUnitState ψ →
        energy (hamZ G w) ψ ≤ energy (hamZ G w) (basisState z)) ∧
      (∀ ψ : Config n → ℂ, IsUnitState ψ →
        energy (hamiltonian G w) ψ ≤ totalWeight G w / 2 + 3 * energy (hamZ G w) (basisState z)) ∧
      energy (hamiltonian G w) (basisState z) =
        totalWeight G w / 2 + energy (hamZ G w) (basisState z) := by sorry

end QMaxCutBeyond.TwoQubit
