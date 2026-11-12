-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_eq_14
-- name    : PDynTreeEmbed.Main.eq_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:31:56.949376+00:00
-- url     : https://prove2.me/theorems/1162fb8c-a879-4376-92cc-20c27ddddb9f
-- title:
--   §5.1, Eq. (14) — P[v ever in the epoch improving set A_i] ≤ 2e(1 + H_n)/i, for insertions and deletions
-- statement:
--   Let $G^{(0)},\dots,G^{(T)}$ be the graphs of a partially dynamic instance (insertions or deletions) fixed in advance, $D>0$, $\pi$ a uniformly random permutation and $R_x\sim\mathrm{Exp}(1/D)$ independent and independent of $\pi$. For every vertex $v$ and every index $i\in[n]$,
--   $$\Pr\Big[v\in\bigcup_t A^{(t)}_i\Big]\le\frac{2e\,(1+H_n)}{i},$$
--   where $A^{(t)}_i$ is the epoch improving set of Definition 5.1 in $G^{(t)}$. It bounds the recourse of the LDD (pp. 30, 45) and the volume in Lemma 5.2.
--
--   Differences from the source:
--
--   - reading: (14) is shown for insertions; p. 22: 'it also holds for edge deletions' → one statement for every instance kind; reason: the paper asserts both
--   - encoding: index i ∈ [n] → position i : Fin n, the paper's index i.val + 1; the bound has denominator i.val + 1; reason: 0-based positions
--   - encoding: R_i drawn per position → radii per vertex, the center at position i uses R_{π(i)} (p. 20 convention); reason: R i.i.d. and independent of π, so the joint law is the same
--   - generalization: polynomially bounded weights W ≤ n^{O(1)} (standing assumption) → any W (the statement has no constant depending on W); reason: the bound W ≤ n^{c_W} is a special case
--   - encoding: uniform π, independent Exp(1/D) radii → any probability space with π measurable of uniform law, iIndepFun R, each R x of law expMeasure (1/D), π independent of R; reason: the statement about every realization of the law
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), pp. 20 and 22, §5.1, Eq. (14)

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Improving
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PDynTreeEmbed.Main

/-- **§5.1, Eq. (14)** (pp. 20, 22). For a partially dynamic instance `G^(0), …, G^(T)` (insertions
or deletions, fixed in advance), `D > 0`, a uniformly random permutation `π` and independent radii
`R_x ∼ Exp(1/D)` independent of `π`: for every vertex `v` and every index `i ∈ [n]`,
`P[v ∈ ⋃_t A^(t)_i] ≤ 2e·(1 + H_n)/i`, where `A^(t)_i` is the epoch improving set of
Definition 5.1. Position `i : Fin n` is the paper's index `i + 1`. -/
theorem eq_14 (n W : ℕ) (G₀ : WGraph (Fin n)) (κ : Kind) (σ : List (Upd n))
    (hinst : IsInstance W G₀ κ σ) (D : ℝ) (hD : 0 < D) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Ω → Equiv.Perm (Fin n)) (R : Fin n → Ω → ℝ)
    (hπ : Measurable π)
    (hπlaw : P.map π = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)
    (hind : iIndepFun R P) (hlaw : ∀ x, P.map (R x) = expMeasure (1 / D))
    (hπR : IndepFun π (fun ω x => R x ω) P) (v : Fin n) (i : Fin n) :
    P {ω | ∃ t ≤ σ.length, v ∈ improvingSet (graphAt G₀ σ t) D (π ω) (fun x => R x ω) i} ≤
      ENNReal.ofReal (2 * Real.exp 1 * (1 + (harmonic n : ℝ)) / ((i.val : ℝ) + 1)) := by sorry

end PDynTreeEmbed.Main
