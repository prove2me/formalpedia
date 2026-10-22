-- Prove2me | Theorems.Thm_QMaxCutBeyond_TwoQubit_eq_27
-- name    : QMaxCutBeyond.TwoQubit.eq_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:16.203234+00:00
-- url     : https://prove2.me/theorems/17c275b7-37d6-4c3d-a012-2e6170704a86
-- title:
--   Eq. (27) — the best of three 1-/2-qubit tensor product states: ratio ≥ max{2f, 3m+W, (4W+f+m)/3}/(2W+f+m)
-- statement:
--   Let $G=(V,E,w)$ have nonnegative weights and $W=\sum_{e\in E}w_e$, and let $M,F\subseteq E$ be a matching and a forest with $\sum_{v\in V}\max_{e\sim v}w_e=m+f$, where $m=\sum_{e\in M}w_e$, $f=\sum_{e\in F}w_e$. Then there is a tensor product $\varphi$ of 1- and 2-qubit states with
--   $$\frac{\langle\varphi|H_G|\varphi\rangle}{\mathrm{OPT}(G)}\;\ge\;\max\Bigl\{\frac{2f}{2W+f+m},\;\frac{3m+W}{2W+f+m},\;\frac13+\frac23\,\frac{W}{2W+f+m}\Bigr\}.$$
--
--   Together with the elementary inequality (28)–(29) this gives Theorem 3.
--
--   **Formalization Note** Stated without division: $\max\{2f,\;3m+W,\;(4W+f+m)/3\}\cdot\langle\psi|H_G|\psi\rangle\le(2W+f+m)\,\langle\varphi|H_G|\varphi\rangle$ for every unit $\psi$ (note $\frac13+\frac23\frac{W}{2W+f+m}=\frac{(4W+f+m)/3}{2W+f+m}$). The state $\varphi$ is chosen before $\psi$.
-- source:
--   Anshu, Gosset & Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394v1, p. 11, eq. (27), proof of Theorem 3

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace QMaxCutBeyond.TwoQubit

/-- Eq. (27), p. 11: if `M ⊆ E` is a matching and `F ⊆ E` a forest with
`Σ_v max_{e∼v} w_e = m + f` (`m = Σ_{e∈M} w_e`, `f = Σ_{e∈F} w_e`), there is a tensor product
`φ` of 1- and 2-qubit states with
`⟨φ|H_G|φ⟩ / OPT(G) ≥ max{2f, 3m + W, (4W + f + m)/3} / (2W + f + m)`, stated without division
for every unit `ψ`. -/
theorem eq_27 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e)
    (M F : Finset (Sym2 (Fin n))) (hMG : M ⊆ G.edgeFinset) (hFG : F ⊆ G.edgeFinset)
    (hM : IsEdgeMatching M) (hF : (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).IsAcyclic)
    (hsum : ∑ v, maxIncident G w v = ∑ e ∈ M, w e + ∑ e ∈ F, w e) :
    ∃ φ : Config n → ℂ, IsOneTwoProduct φ ∧ ∀ ψ : Config n → ℂ, IsUnitState ψ →
      max (2 * ∑ e ∈ F, w e)
          (max (3 * ∑ e ∈ M, w e + totalWeight G w)
            ((4 * totalWeight G w + ∑ e ∈ F, w e + ∑ e ∈ M, w e) / 3)) *
          energy (hamiltonian G w) ψ ≤
        (2 * totalWeight G w + ∑ e ∈ F, w e + ∑ e ∈ M, w e) * energy (hamiltonian G w) φ := by sorry

end QMaxCutBeyond.TwoQubit
