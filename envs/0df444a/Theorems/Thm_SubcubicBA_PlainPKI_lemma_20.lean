-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_lemma_20
-- name    : SubcubicBA.PlainPKI.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:43:06.304149+00:00
-- url     : https://prove2.me/theorems/17849e8d-3af7-4913-af2a-86f70e2014f1
-- title:
--   Lemma 20 — Ramanujan bipartite all-neighbours-in-S bound
-- statement:
--   Let $G$ be a $D$-regular bipartite Ramanujan graph with $n$ vertices on each side $L$ and $R$ (a multigraph is allowed), with $D\ge1$. Let $S$ be a proper subset of $L$ and let $H=\{v\in R: N(v)\subseteq S\}$ be the set of right vertices all of whose edges come from $S$. Then
--   $$|H|\le\frac{4|S|}{D\,(1-|S|/n)^2}.$$
--
--   The bound converts spectral expansion into the statement that few right vertices can be fully captured by a small left set; it drives the fault-tolerant expander of Theorem 2.
--
--   Differences from the source:
--   - reading: H = {v ∈ R, N(v) ⊆ H} (circular as printed) → H = {v ∈ R : N(v) ⊆ S}; reason: the parenthetical: H is the set of nodes whose edges all come from S (paper.md item 4)
--   - reading: S ⊂ L → S a proper subset of L; reason: at S = L the denominator (1 − |S|/n)² vanishes; ⊂ is read as proper
--   - generalization: a D-regular Ramanujan bipartite graph → a D-regular bipartite multigraph (biadjacency multiplicity matrix) whose second singular value is at most 2√(D−1); reason: simple graphs are the 0/1 case; the expander mixing argument of the proof applies verbatim
--   - encoding: √(D − 1) in the Ramanujan bound → the hypothesis 1 ≤ D; reason: excludes only the undefined case D = 0
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Lemma 20, p. 38

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Graphs

namespace SubcubicBA.PlainPKI

/-- Lemma 20 (p. 38). -/
theorem lemma_20 (D n : ℕ) (N : Fin n → Fin n → ℕ) (hD : 1 ≤ D) (hR : IsRamanujanBip D n N)
    (S : Finset (Fin n)) (hS : S ≠ Finset.univ) :
    ((Finset.univ.filter fun v : Fin n => ∀ u : Fin n, 0 < N u v → u ∈ S).card : ℝ) ≤
      4 * (S.card : ℝ) / ((D : ℝ) * (1 - (S.card : ℝ) / n) ^ 2) := by sorry

end SubcubicBA.PlainPKI
