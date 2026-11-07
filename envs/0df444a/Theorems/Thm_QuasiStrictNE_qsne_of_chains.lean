-- Prove2me | Theorems.Thm_QuasiStrictNE_qsne_of_chains
-- name    : QuasiStrictNE.qsne_of_chains
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:59.11159+00:00
-- url     : https://prove2.me/theorems/7b2aa9c4-2b33-4164-98e9-badc2b1fce42
-- title:
--   p.13 — $(p_{F_r},q_{G_0})$ is a quasi-strict equilibrium
-- statement:
--   Let $(A,B)$ be a bimatrix game with relative-interior points $p_F$, $q_G$ fixed for the faces of $\mathcal C_m$, $\mathcal C_n$. Let $F_0\subsetneq\cdots\subsetneq F_r$ be a chain in $\mathcal C_m$ and $G_0\subsetneq\cdots\subsetneq G_s$ a chain in $\mathcal C_n$, with strictly positive weights $\lambda_t$, $\mu_u$ summing to $1$, such that (7) and (8) hold:
--   $$
--   \sum_{t=0}^r\lambda_t\,\ell_m(\mathrm{supp}(p_{F_t}))=\sum_{u=0}^s\mu_u\,\ell_m(BR_1(q_{G_u})),\qquad
--   \sum_{u=0}^s\mu_u\,\ell_n(\mathrm{supp}(q_{G_u}))=\sum_{t=0}^r\lambda_t\,\ell_n(BR_2(p_{F_t})).
--   $$
--   Then $(p_{F_r},q_{G_0})$ is a quasi-strict Nash equilibrium:
--   $$
--   \mathrm{supp}(p_{F_r})=BR_1(q_{G_0}),\qquad \mathrm{supp}(q_{G_0})=BR_2(p_{F_r}).
--   $$
--
--   Differences from the source:
--   - encoding: relint F (interior in the affine hull); a fixed point pF per face → intrinsicInterior ℝ F; the selection is a function p on sets with p F ∈ intrinsicInterior ℝ F for F in the complex; reason: Lean convention; same selections
--   - generalization: the chains of the unique minimal simplices of Km, Kn containing the fixed point (x̄, ȳ), with its barycentric weights → every pair of chains with strictly positive weights summing to 1 that satisfies (7)–(8); reason: the paper's argument uses only the positivity of the weights; its minimal simplices are one such pair
--   - encoding: S1(x̄) = R1(ȳ), S2(ȳ) = R2(x̄) rewritten with (2) as (7)–(8) → the hypotheses are the sums (7) and (8) themselves; reason: these are the paper's equations (7)–(8)
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), proof of Theorem 5, p.13

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_BR1
import Definitions.Def_QuasiStrictNE_BR2
import Definitions.Def_QuasiStrictNE_IsQSNE
import Definitions.Def_QuasiStrictNE_Cm
import Definitions.Def_QuasiStrictNE_Cn
import Definitions.Def_QuasiStrictNE_IsFaceChain
import Definitions.Def_QuasiStrictNE_ell

namespace QuasiStrictNE

/-- **Extraction of a quasi-strict equilibrium from (7)–(8)** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, proof of Theorem 5, p.13: "We
claim that (pFr, qG0) is a quasi-strict Nash equilibrium. By Definition 1, verify the conditions
supp(pFr) = BR1(qG0), supp(qG0) = BR2(pFr)").

Let `(A, B)` be a bimatrix game, and let `p`, `q` select relative-interior points of the faces of
`Cm`, `Cn`. Let `F₀ ⊊ ⋯ ⊊ F_r` be a chain of `Cm` with largest member `F_r`, `G₀ ⊊ ⋯ ⊊ G_s` a chain of
`Cn` with smallest member `G₀`, and `λ`, `μ` strictly positive weights on them, each summing to `1`. If
(7) and (8) hold,
`∑ λ_t ℓm(supp(p F_t)) = ∑ μ_u ℓm(BR1(q G_u))` and `∑ μ_u ℓn(supp(q G_u)) = ∑ λ_t ℓn(BR2(p F_t))`,
then `(p F_r, q G₀)` is a quasi-strict Nash equilibrium.

**Formalization Note** The paper takes the chains of the minimal simplices of `Km`, `Kn` containing
the fixed point; its argument uses only that the weights are strictly positive, so the statement is
made for every chain with positive weights. Chains are `Finset`s of faces totally ordered by `⊆`. -/
theorem qsne_of_chains {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ)
    (p : Set (Fin m → ℝ) → (Fin m → ℝ)) (q : Set (Fin n → ℝ) → (Fin n → ℝ))
    (hp : ∀ F ∈ Cm B, p F ∈ intrinsicInterior ℝ F)
    (hq : ∀ G ∈ Cn A, q G ∈ intrinsicInterior ℝ G)
    (σ : Finset (Set (Fin m → ℝ))) (τ : Finset (Set (Fin n → ℝ)))
    (hσ : IsFaceChain (Cm B) σ) (hτ : IsFaceChain (Cn A) τ)
    (lam : Set (Fin m → ℝ) → ℝ) (mu : Set (Fin n → ℝ) → ℝ)
    (hlam : ∀ F ∈ σ, 0 < lam F) (hlam1 : ∑ F ∈ σ, lam F = 1)
    (hmu : ∀ G ∈ τ, 0 < mu G) (hmu1 : ∑ G ∈ τ, mu G = 1)
    (h7 : ∑ F ∈ σ, lam F • ell m (supp (p F)) = ∑ G ∈ τ, mu G • ell m (BR1 A (q G)))
    (h8 : ∑ G ∈ τ, mu G • ell n (supp (q G)) = ∑ F ∈ σ, lam F • ell n (BR2 B (p F)))
    (Fr : Set (Fin m → ℝ)) (hFr : Fr ∈ σ) (hFr_max : ∀ F ∈ σ, F ⊆ Fr)
    (G0 : Set (Fin n → ℝ)) (hG0 : G0 ∈ τ) (hG0_min : ∀ G ∈ τ, G0 ⊆ G) :
    IsQSNE A B (p Fr) (q G0) := by sorry

end QuasiStrictNE
