-- Prove2me | Theorems.Thm_TermCycDich_Supplement_theorem_4_3
-- name    : TermCycDich.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:52:50.253147+00:00
-- url     : https://prove2.me/theorems/297d21ed-5407-408b-a1ab-0c55b7e73fe1
-- title:
--   Theorem 4.3 — every thirsty $(w,b)$-village of a vital instance has $w\le7\lfloor\log_3|G|\rfloor+7$
-- statement:
--   Let $\mathcal V=(G,R,S,A,\rho,\Sigma,\Delta,\mathcal C)$ be a thirsty $(w,b)$-village for a vital instance $(G,R)$. Then
--
--   $$w\le 7\lfloor\log_3|G|\rfloor+7 .$$
--
--   Together with Theorem 3.9 this gives Theorem 1.3: a vital instance whose treewidth exceeds $f_{3.9}(b,7\lfloor\log_3|G|\rfloor+8)\in\mathrm{poly}(b)\cdot\log|G|$ would contain a thirsty village that is too deep.
--
--   **Formalization Note** The statement holds for every choice of the functions $\mathrm{apex}$, $\mathrm{depth}$ entering the village definition, in particular for those of Proposition 2.4.
--
--   Differences from the source:
--   - generalization: a thirsty village relative to the functions apex2.4, depth2.4 of Proposition 2.4 → a thirsty village relative to arbitrary functions apex, depth : ℕ → ℕ → ℕ → ℕ; reason: the bound on w does not depend on these functions; it specializes to the paper's apex2.4, depth2.4
--   - encoding: ⌊log₃ |G|⌋ → Nat.log 3 (Fintype.card V); reason: floor logarithm on ℕ; |G| ≥ 3 for a vital instance
--   - encoding: surface Σ, Σ-rendition ρ of G − A, traces, C-discs → a type X with IsSurface, the supplement's Rendition of minusVerts G A, traces as relations ('some trace' where a trace is asserted to lie somewhere), the C-disc inside the specified disc; Euler genus < g as Σ(h,c) minus open discs with 2h + c < g; reason: the paper defines traces only up to a slight push; every property used is invariant under the push; Euler genus of a surface with boundary is that of its capped surface
--   - reading: the cycles of C are tight; W is a dry w-well with the induced rendition ρ_Δ → tightness for C_i-paths of the crop by Δ; legs as path subgraphs of S; well conditions stated through ρ inside Δ; the drained condition for every choice of the interior Δ_P; reason: tightness is asserted for the village's rendition inside Δ; ρ_Δ draws exactly these paths and cycles in the cells of ρ inside Δ; Δ_P is unique
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 4.3, p.32 (PDF 34)

import Mathlib
import Definitions.Def_TermCycDich_Supplement_Thirsty

namespace TermCycDich

namespace Supplement

open GMSTFramework.LocalStructure

/-- **Theorem 4.3** (thirsty villages are logarithmically small).

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held
version, sha256 34a10f1a…4d4ea1), Theorem 4.3, p.32 (PDF 34): "Let V = (G, R, S, A, ρ, Σ, ∆, C)
be a thirsty (w, b)-village for a vital instance (G, R). Then, w ≤ 7⌊log₃ |G|⌋ + 7."

**Formalization Note** The village definition refers to the functions `apex2.4`, `depth2.4` of the
cited Proposition 2.4; the statement is made for every choice of these two functions (the paper's
choice is one of them). `⌊log₃ |G|⌋` is `Nat.log 3 |V(G)|`; vitality of `(G, R)` is part of
`IsVillage`. -/
theorem theorem_4_3 (apex depth : ℕ → ℕ → ℕ → ℕ) (w b : ℕ) {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (R : Set V) {u : V} (S : G.Walk u u) (A : Finset V)
    (X : Type) [TopologicalSpace X] (ρ : Rendition X (minusVerts G (A : Set V))) (Δ : Set X)
    (C : Fin w → G.Subgraph)
    (hV : IsThirstyVillage apex depth w b G R S A X ρ Δ C) :
    w ≤ 7 * Nat.log 3 (Fintype.card V) + 7 := by sorry

end Supplement

end TermCycDich
