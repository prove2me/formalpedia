-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_lemma_5_2
-- name    : PDynTreeEmbed.Main.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:31:49.783445+00:00
-- url     : https://prove2.me/theorems/7094afb0-f1b7-468c-803e-6c2b303dde8a
-- title:
--   Lemma 5.2 — the epoch improving sets have total expected volume O(m log² n)
-- statement:
--   There is a universal constant $C$ such that, for every partially dynamic instance $G^{(0)},\dots,G^{(T)}$ on $n\ge2$ vertices fixed in advance (an oblivious adversary), every $D>0$, a uniformly random permutation $\pi$ and independent radii $R_x\sim\mathrm{Exp}(1/D)$ independent of $\pi$,
--   $$\mathbb E\Big[\sum_i\mathrm{vol}\Big(\bigcup_t A^{(t)}_i\Big)\Big]\le C\,m\,\log_2^2 n,$$
--   volumes measured in the graph holding every edge ever present, which has $m$ edges. This bounds the total size of the local graphs on which the dynamic algorithms run.
--
--   Differences from the source:
--
--   - generalization: graphs undergoing edge insertions, volumes in the final graph → also deletions, volumes in the initial graph (unionGraph); reason: (14) holds for deletions (p. 22) and the decremental proof (p. 45) uses the same bound; κ = incr is the printed statement
--   - encoding: O(m log² n) → an explicit universal constant C > 0, quantified before the graph, the level, the execution and the law; reason: the meaning of O(·)
--   - encoding: n vertices (α = 1/(2 log n) and log n need n ≥ 2) → hypothesis 2 ≤ n; reason: the only excluded case n = 1 makes log₂ n = 0 and α undefined
--   - generalization: polynomially bounded weights W ≤ n^{O(1)} (standing assumption) → any W (the statement has no constant depending on W); reason: the bound W ≤ n^{c_W} is a special case
--   - encoding: uniform π, independent Exp(1/D) radii → any probability space with π measurable of uniform law, iIndepFun R, laws expMeasure (1/D), π independent of R; expectation as a lintegral; reason: the statement about every realization of the law
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 20, Lemma 5.2

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Improving
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PDynTreeEmbed.Main

/-- **Lemma 5.2** (p. 20). There is a universal constant `C` such that for every partially
dynamic instance `G^(0), …, G^(T)` on `n ≥ 2` vertices fixed in advance (insertions; also deletions), every
`D > 0`, a uniformly random permutation `π` and independent radii `R_x ∼ Exp(1/D)` independent of
`π`: `E[Σ_i vol(⋃_t A^(t)_i)] ≤ C·m·(log₂ n)²`, where volumes are measured in the graph holding
every edge ever present (the final graph for insertions, the initial one for deletions), which has
`m` edges. -/
theorem lemma_5_2 : ∃ C : ℝ, 0 < C ∧
    ∀ (n W : ℕ) (G₀ : WGraph (Fin n)) (κ : Kind) (σ : List (Upd n)), 2 ≤ n →
      IsInstance W G₀ κ σ → ∀ (D : ℝ), 0 < D →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (π : Ω → Equiv.Perm (Fin n)) (R : Fin n → Ω → ℝ), Measurable π →
        P.map π = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure →
        iIndepFun R P → (∀ x, P.map (R x) = expMeasure (1 / D)) →
        IndepFun π (fun ω x => R x ω) P →
        ∫⁻ ω, ∑ i : Fin n, ((unionGraph G₀ κ σ).vol ((Finset.range (σ.length + 1)).biUnion
            fun t => improvingSet (graphAt G₀ σ t) D (π ω) (fun x => R x ω) i) : ℝ≥0∞) ∂P ≤
          ENNReal.ofReal (C * (totalEdges G₀ σ : ℝ) * log2 n ^ 2) := by sorry

end PDynTreeEmbed.Main
