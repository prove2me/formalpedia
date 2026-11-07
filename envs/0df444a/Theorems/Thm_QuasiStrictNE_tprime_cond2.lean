-- Prove2me | Theorems.Thm_QuasiStrictNE_tprime_cond2
-- name    : QuasiStrictNE.tprime_cond2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:13:30.582199+00:00
-- url     : https://prove2.me/theorems/3d217ce4-5054-46d5-bc25-cfdd689a34c7
-- title:
--   pp.15–16 — $T'$ satisfies the second condition of Definition 6
-- statement:
--   Choose the points $p_F$, $q_G$ for every $F\in\mathcal C_m$ and $G\in\mathcal C_n$ by Lemma 3. Then, over the rational bimatrix games $I$ with $m,n\ge 1$, the map
--   $$
--   T'(x,y)=\bigl(\Pi_m\circ h_1(x,y),\ \Pi_n\circ h_2(x,y)\bigr)
--   $$
--   on $\Delta_m\times\Delta_n\subseteq\mathbb R^{m+n}$ satisfies the second condition of Definition 6: there are rational dividing hyperplanes such that $T'$ is affine on every closed region, and all coefficients of the hyperplanes and affine formulas have encoding length polynomial in $|I|$.
--
--   Differences from the source:
--   - generalization: the selection pF, qG computed by the paper's fixed deterministic LP algorithm (Lemma 3, p.14; p.15 'Choose the points pF and qG … using Lemma 3') → every pair of polynomial-time maps with the Lemma 3 property (IsLPSelection) and the selections selP, selQ they compute; reason: the paper's LP selection has the Lemma 3 property, so the statement specializes to it
--   - reading: a collection of hyperplanes dividing DI into polyhedral regions on each of which FI is affine, coefficients of encoding length polynomial in |I| uniformly → a finite set of rational hyperplanes (a pair with a = 0 is allowed and cuts nothing); on every closed sign cell intersected with the domain a rational affine formula; every coefficient of encoding length ≤ q(|I|) for one polynomial q; reason: the paper's own regions R_T are closed (p.16, 'including its boundary'); the number of hyperplanes is not bounded (p.16 uses one per subset T)
--   - encoding: T′ on Δm × Δn ⊆ ℝ^{m+n} → TprimeFlat on Fin (m + n) → ℝ (Fin.append of the two parts), domain DeltaProd m n; reason: Lean convention; same map
--   - encoding: for each input game I → for each rational game with m, n ≥ 1 (a subtype of RatGame), size = length of its code; reason: Definition 1 and the standing k ≥ 1; the game code is the input I
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §4, pp.15–16

import Mathlib
import Definitions.Def_QuasiStrictNE_RatGame
import Definitions.Def_QuasiStrictNE_RatGame_enc
import Definitions.Def_QuasiStrictNE_PLCond2
import Definitions.Def_QuasiStrictNE_DeltaProd
import Definitions.Def_QuasiStrictNE_TprimeFlat
import Definitions.Def_QuasiStrictNE_IsLPSelection
import Definitions.Def_QuasiStrictNE_selP
import Definitions.Def_QuasiStrictNE_selQ

namespace QuasiStrictNE

/-- **`T′` satisfies the second condition of Definition 6** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, §4, pp.15–16: "Using Lemma 4,
the composition maps Πm◦h1 and Πn◦h2 also meet the second condition in Definition 6. Taking the union
of the dividing hyperplane collections for the two composition maps gives regions on which both affine
formulas apply. Concatenating these formulas also satisfies the second condition"; p.15: "Choose the
points pF and qG for every F ∈ Cm and G ∈ Cn using Lemma 3").

Let `gP`, `gQ` be maps with the Lemma 3 property and `selP`, `selQ` the selections they compute. Over
the rational bimatrix games `I` with `m, n ≥ 1`, the map `T′ : ℝ^{m+n} → ℝ^{m+n}` built with these
selections satisfies condition 2 of Definition 6 on `Δm × Δn`, with sizes `|I|`: finitely many
hyperplanes and affine formulas on the closed cells, all with rational coefficients of encoding length
polynomial in `|I|`.

**Formalization Note** The statement holds for every polynomial-time selection with the Lemma 3
property, the paper's LP selection being one of them. `ℝ^{m+n}` is `Fin (m + n) → ℝ`. -/
theorem tprime_cond2 (gP gQ : List Bool → List Bool) (hg : IsLPSelection gP gQ) :
    PLCond2 (ι := {G : RatGame // 1 ≤ G.m ∧ 1 ≤ G.n}) (fun G => G.1.enc.length)
      (fun G => G.1.m + G.1.n) (fun G => G.1.m + G.1.n) (fun G => DeltaProd G.1.m G.1.n)
      (fun G => TprimeFlat (G.1.A.map ((↑) : ℚ → ℝ)) (G.1.B.map ((↑) : ℚ → ℝ))
        (selP gP G.1) (selQ gQ G.1)) := by sorry

end QuasiStrictNE
