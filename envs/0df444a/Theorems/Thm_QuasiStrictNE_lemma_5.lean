-- Prove2me | Theorems.Thm_QuasiStrictNE_lemma_5
-- name    : QuasiStrictNE.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:13:27.03181+00:00
-- url     : https://prove2.me/theorems/8bb2c391-d2c3-408f-afaf-461e9900e14d
-- title:
--   Lemma 5 — a linear-comparison oracle algorithm for the local formula of $T'$
-- statement:
--   Choose the points $p_F$, $q_G$ by Lemma 3. Given a rational bimatrix game $I$ (with $m,n\ge 1$), there exists a polynomial-time algorithm with access to a linear-comparison oracle for $z\in\mathbb R^{m+n}$ that outputs **No** if $z\notin\Delta_m\times\Delta_n$; otherwise it returns the local formula of $T'$ at $z$: a rational matrix $C$ and vector $c$ with
--   $$
--   T'(z)=Cz+c.
--   $$
--   One algorithm serves all games, and its running time is polynomial in $|I|$.
--
--   Differences from the source:
--   - generalization: the selection pF, qG computed by the paper's fixed deterministic LP algorithm (Lemma 3, p.14; p.15 'Choose the points pF and qG … using Lemma 3') → every pair of polynomial-time maps with the Lemma 3 property (IsLPSelection) and the selections selP, selQ they compute; reason: the paper's LP selection has the Lemma 3 property, so the statement specializes to it
--   - reading: it returns the local formula T′(z) → it outputs rational (C, c) with T′(z) = Cz + c; reason: Definition 6.3: 'outputs a rational matrix C and a rational vector c … so that FI(x) = Cx + c'
--   - encoding: a polynomial-time algorithm interacting with a linear-comparison oracle → one step function, PolyTimeComputable on (instance, answers so far), run for q(|I|) rounds; queries coded by encRatVec/encRat, malformed queries answered false; output No = [false, false], or the tagged code of (C, c); reason: a model of the paper's oracle algorithms; every step and the whole run are polynomial in |I|
--   - encoding: T′ on Δm × Δn ⊆ ℝ^{m+n} → TprimeFlat on Fin (m + n) → ℝ (Fin.append of the two parts), domain DeltaProd m n; reason: Lean convention; same map
--   - encoding: for each input game I → for each rational game with m, n ≥ 1 (a subtype of RatGame), size = length of its code; reason: Definition 1 and the standing k ≥ 1; the game code is the input I
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Lemma 5, p.16

import Mathlib
import Definitions.Def_QuasiStrictNE_RatGame
import Definitions.Def_QuasiStrictNE_RatGame_enc
import Definitions.Def_QuasiStrictNE_OracleComputesLocalFormula
import Definitions.Def_QuasiStrictNE_DeltaProd
import Definitions.Def_QuasiStrictNE_TprimeFlat
import Definitions.Def_QuasiStrictNE_IsLPSelection
import Definitions.Def_QuasiStrictNE_selP
import Definitions.Def_QuasiStrictNE_selQ

namespace QuasiStrictNE

/-- **Lemma 5** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict Equilibria*,
arXiv:2611.06350, Lemma 5, p.16: "Given a rational bimatrix game I, there exists a polynomial-time
algorithm with access to a linear-comparison oracle for z ∈ R^{m+n} that outputs No if z ∉ ∆m × ∆n.
Otherwise, it returns the local formula T′(z)").

Let `gP`, `gQ` be maps with the Lemma 3 property and `selP`, `selQ` the selections they compute. There
is one polynomial-time linear-comparison oracle algorithm that, given the code of a rational bimatrix
game `I` with `m, n ≥ 1` and oracle access to `z ∈ ℝ^{m+n}`, outputs `No` if `z ∉ Δm × Δn`, and
otherwise a rational matrix `C` and vector `c` with `T′(z) = Cz + c`.

**Formalization Note** "Returns the local formula T′(z)" is read as in Definition 6.3: rational
`(C, c)` with `T′(z) = Cz + c`. One algorithm serves all games; its running time is polynomial in
`|I|`. The statement holds for every selection with the Lemma 3 property (the paper's LP selection is
one of them). -/
theorem lemma_5 (gP gQ : List Bool → List Bool) (hg : IsLPSelection gP gQ) :
    OracleComputesLocalFormula (ι := {G : RatGame // 1 ≤ G.m ∧ 1 ≤ G.n}) (fun G => G.1.enc)
      (fun G => G.1.m + G.1.n) (fun G => G.1.m + G.1.n) (fun G => DeltaProd G.1.m G.1.n)
      (fun G => TprimeFlat (G.1.A.map ((↑) : ℚ → ℝ)) (G.1.B.map ((↑) : ℚ → ℝ))
        (selP gP G.1) (selQ gQ G.1)) := by sorry

end QuasiStrictNE
