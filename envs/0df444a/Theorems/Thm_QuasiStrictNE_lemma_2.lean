-- Prove2me | Theorems.Thm_QuasiStrictNE_lemma_2
-- name    : QuasiStrictNE.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:12:42.392268+00:00
-- url     : https://prove2.me/theorems/96bf2377-18e5-4d62-be0a-8f2c334fa880
-- title:
--   Lemma 2 — fixed points of $T'$ satisfy $S_1(x)=R_1(y)$, $S_2(y)=R_2(x)$
-- statement:
--   Let $(A,B)$ be a bimatrix game with $m,n\ge 1$, fix relative-interior points $p_F$, $q_G$ of the faces of $\mathcal C_m$, $\mathcal C_n$, and let $T'(x,y)=(\Pi_m(h_1(x,y)),\Pi_n(h_2(x,y)))$ with $h_1=x+R_1(y)-S_1(x)$, $h_2=y+R_2(x)-S_2(y)$. If $(x,y)$ is a fixed point of $T'$, then
--   $$
--   S_1(x)=R_1(y)\qquad\text{and}\qquad S_2(y)=R_2(x).
--   $$
--
--   Differences from the source:
--   - encoding: relint F (interior in the affine hull); a fixed point pF per face → intrinsicInterior ℝ F; the selection is a function p on sets with p F ∈ intrinsicInterior ℝ F for F in the complex; reason: Lean convention; same selections
--   - encoding: a fixed point (x, y) of T′ : Δm × Δn → Δm × Δn → x : ℝ^m, y : ℝ^n with Tprime A B p q (x, y) = (x, y); reason: T′ takes values in Δm × Δn (Lemma 1), so the fixed points are the same
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Lemma 2, p.14

import Mathlib
import Definitions.Def_QuasiStrictNE_Cm
import Definitions.Def_QuasiStrictNE_Cn
import Definitions.Def_QuasiStrictNE_S1
import Definitions.Def_QuasiStrictNE_R2
import Definitions.Def_QuasiStrictNE_S2
import Definitions.Def_QuasiStrictNE_R1
import Definitions.Def_QuasiStrictNE_Tprime

namespace QuasiStrictNE

/-- **Lemma 2** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict Equilibria*,
arXiv:2611.06350, Lemma 2, p.14: "A fixed point (x, y) of T′ implies S1(x) = R1(y) and
S2(y) = R2(x)").

Let `(A, B)` be a bimatrix game with `m, n ≥ 1`, and let `p`, `q` select relative-interior points of
the faces of `Cm`, `Cn`. If `T′(x, y) = (x, y)`, then `S1(x) = R1(y)` and `S2(y) = R2(x)`.

**Formalization Note** The selections are arbitrary relative-interior selections. A fixed point of
`T′` lies in `Δm × Δn` automatically, since `T′` takes values there (Lemma 1), so no membership
hypothesis is stated. -/
theorem lemma_2 {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (A B : Matrix (Fin m) (Fin n) ℝ)
    (p : Set (Fin m → ℝ) → (Fin m → ℝ)) (q : Set (Fin n → ℝ) → (Fin n → ℝ))
    (hp : ∀ F ∈ Cm B, p F ∈ intrinsicInterior ℝ F)
    (hq : ∀ G ∈ Cn A, q G ∈ intrinsicInterior ℝ G)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (hfix : Tprime A B p q (x, y) = (x, y)) :
    S1 B p x = R1 A q y ∧ S2 A q y = R2 B p x := by sorry

end QuasiStrictNE
