-- Prove2me | Theorems.Thm_QMaxCutBeyond_TwoQubit_eq_24
-- name    : QMaxCutBeyond.TwoQubit.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:11.687216+00:00
-- url     : https://prove2.me/theorems/5f851460-efd0-4b09-86c4-2ecac4e439a8
-- title:
--   Eq. (24) — a basis state reaches 1/3 + 2/3 · W/(2W + Σ_v max_{e∼v} w_e) of OPT(G)
-- statement:
--   Let $G=(V,E,w)$ have nonnegative weights, $W=\sum_{e\in E}w_e$ and $S=\sum_{v\in V}\max_{e\sim v}w_e$. There is a computational basis state $|z\rangle$ (in particular a product state) with
--   $$\frac{\langle z|H_G|z\rangle}{\mathrm{OPT}(G)}\;\ge\;\frac13+\frac23\,\frac{W}{2W+S},$$
--   so that $\mathrm{PROD}(G)/\mathrm{OPT}(G)$ is at least the same quantity.
--
--   This is the third of the three candidate states combined in eq. (27).
--
--   **Formalization Note** Stated without division: $3(2W+S)\langle z|H_G|z\rangle\ge(4W+S)\langle\psi|H_G|\psi\rangle$ for every unit $\psi$, which is equivalent when $2W+S>0$ and trivial otherwise (then $H_G=0$). The paper states the bound for $\mathrm{PROD}(G)$; the item names the basis-state witness, as the "Moreover" of Theorem 5 does in the unweighted case.
-- source:
--   Anshu, Gosset & Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394v1, p. 10, eq. (24), proof of Theorem 3

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace QMaxCutBeyond.TwoQubit

/-- Eq. (24), p. 10, with a computational basis state as the product state:
there is `z` with `⟨z|H_G|z⟩ / OPT(G) ≥ 1/3 + 2/3 · W / (2W + S)`, `S = Σ_v max_{e∼v} w_e`,
stated without division: `3 (2W + S) ⟨z|H_G|z⟩ ≥ (4W + S) ⟨ψ|H_G|ψ⟩` for every unit `ψ`. -/
theorem eq_24 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e) :
    ∃ z : Config n, ∀ ψ : Config n → ℂ, IsUnitState ψ →
      (4 * totalWeight G w + ∑ v, maxIncident G w v) * energy (hamiltonian G w) ψ ≤
        3 * (2 * totalWeight G w + ∑ v, maxIncident G w v) *
          energy (hamiltonian G w) (basisState z) := by sorry

end QMaxCutBeyond.TwoQubit
