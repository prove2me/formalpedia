-- Prove2me | Theorems.Thm_QuasiStrictNE_eq_3_4
-- name    : QuasiStrictNE.eq_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:18.858704+00:00
-- url     : https://prove2.me/theorems/aa9a87ab-70ea-4928-9ee8-5e90c91b5c28
-- title:
--   Equations (3)–(4) — supports grow and best responses shrink along face inclusions
-- statement:
--   Let $(A,B)$ be a bimatrix game and fix points $p_F\in\mathrm{relint}\,F$ for $F\in\mathcal C_m$ and $q_G\in\mathrm{relint}\,G$ for $G\in\mathcal C_n$. If $F\subseteq F'$ are faces of $\mathcal C_m$, then
--   $$
--   \mathrm{supp}(p_F)\subseteq\mathrm{supp}(p_{F'}),\qquad BR_2(p_F)\supseteq BR_2(p_{F'}),\tag{3}
--   $$
--   and if $G\subseteq G'$ are faces of $\mathcal C_n$, then
--   $$
--   \mathrm{supp}(q_G)\subseteq\mathrm{supp}(q_{G'}),\qquad BR_1(q_G)\supseteq BR_1(q_{G'}).\tag{4}
--   $$
--   These inclusions make the four vertex maps (2) simplicial.
--
--   Differences from the source:
--   - encoding: relint F (interior in the affine hull); a fixed point pF per face → intrinsicInterior ℝ F; the selection is a function p on sets with p F ∈ intrinsicInterior ℝ F for F in the complex; reason: Lean convention; same selections
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), proof of Theorem 5, (3)–(4), p.11

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_BR1
import Definitions.Def_QuasiStrictNE_BR2
import Definitions.Def_QuasiStrictNE_Cm
import Definitions.Def_QuasiStrictNE_Cn

namespace QuasiStrictNE

/-- **Equations (3) and (4): monotonicity along face inclusions** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, proof of Theorem 5, p.11: "If
F ⊆ F′, then supp(pF) ⊆ supp(pF′), BR2(pF) ⊇ BR2(pF′). (3)" and "These arguments are identical for
G ⊆ G′, supp(qG) ⊆ supp(qG′), BR1(qG) ⊇ BR1(qG′). (4)").

Let `(A, B)` be a bimatrix game and let `p`, `q` select a point of the relative interior of every face
of `Cm`, `Cn`. For faces `F ⊆ F′` of `Cm`, the support of `p F` is contained in that of `p F′` and the
best responses of player 2 to `p F′` are among those to `p F`; for faces `G ⊆ G′` of `Cn`, the support
of `q G` is contained in that of `q G′` and the best responses of player 1 to `q G′` are among those to
`q G`.

**Formalization Note** The selections are arbitrary relative-interior selections (paper (1), p.10);
`relint` is `intrinsicInterior ℝ`. -/
theorem eq_3_4 {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ)
    (p : Set (Fin m → ℝ) → (Fin m → ℝ)) (q : Set (Fin n → ℝ) → (Fin n → ℝ))
    (hp : ∀ F ∈ Cm B, p F ∈ intrinsicInterior ℝ F)
    (hq : ∀ G ∈ Cn A, q G ∈ intrinsicInterior ℝ G) :
    (∀ F ∈ Cm B, ∀ F' ∈ Cm B, F ⊆ F' →
      supp (p F) ⊆ supp (p F') ∧ BR2 B (p F') ⊆ BR2 B (p F)) ∧
    (∀ G ∈ Cn A, ∀ G' ∈ Cn A, G ⊆ G' →
      supp (q G) ⊆ supp (q G') ∧ BR1 A (q G') ⊆ BR1 A (q G)) := by sorry

end QuasiStrictNE
