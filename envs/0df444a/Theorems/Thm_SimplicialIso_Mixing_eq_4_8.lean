-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_eq_4_8
-- name    : SimplicialIso.Mixing.eq_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:10.745967+00:00
-- url     : https://prove2.me/theorems/b169b332-9d08-44fb-8708-1e653c25112d
-- title:
--   (4.8), p. 17 — |F(A_0,…,A_d)| = α⟨φ, ℙ_{B^{d−1}}ψ⟩ + ⟨φ, (αI − Δ⁺)ℙ_{Z_{d−1}}ψ⟩
-- statement:
--   Let $X$, $d\ge1$, the pairwise disjoint sets $A_0,\dots,A_d$ and $\varphi,\psi$ be as in (4.6), and let $\alpha\in\mathbb R$. Using the orthogonal decomposition $\Omega^{d-1}=B^{d-1}\oplus Z_{d-1}$ and $B^{d-1}\subseteq\ker\Delta^+$,
--   $$|F(A_0,A_1,\dots,A_d)|=\alpha\langle\varphi,\mathbb P_{B^{d-1}}\psi\rangle+\langle\varphi,(\alpha I-\Delta^+)\mathbb P_{Z_{d-1}}\psi\rangle.\qquad(4.8)$$
--
--   The first term is the expected count, the second the error term of the Mixing Lemma.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, §4.3, p. 17, equation (4.8)

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting
import Definitions.Def_SimplicialIso_Mixing_DeltaForms

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- (4.8), p. 17: for disjoint `A_0, …, A_d` and every `α`,
`|F(A_0, …, A_d)| = α ⟨φ, ℙ_{B^{d-1}} ψ⟩ + ⟨φ, (αI − Δ⁺) ℙ_{Z_{d-1}} ψ⟩`. -/
theorem eq_4_8 (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) (A : Fin (d + 1) → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (α : ℝ) :
    ((F X A).card : ℝ) =
      α * ⟪phi A, projExact n d (psi A)⟫_ℝ +
        ⟪phi A, (α • LinearMap.id - upLap X : Form n d →ₗ[ℝ] Form n d) (projCycles n d (psi A))⟫_ℝ := by sorry

end SimplicialIso.Mixing
