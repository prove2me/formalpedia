-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_observation_4_11
-- name    : SmallSecretLWE.Classical.observation_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:28:06.774408+00:00
-- url     : https://prove2.me/theorems/27c30aae-ed85-437c-a1fa-f77f0f72564e
-- title:
--   Observation 4.11 — $K_l(A)$ has reverse edges and its row coloring is 2-deficient
-- statement:
--   Let $A\in\mathbb Z_q^{m\times n}$ have rows with exactly $k$ nonzero entries and $l\ge k/2$. Every edge $e=(u,v)$ of $K_l(A)$ has a reverse edge $e^{\mathrm{rev}}=(v,u)$, and coloring both by the row index $i$ with $v-u=\pm a_i$ makes $K_l(A)$ a **2-deficient** edge-colored directed graph: every vertex has at most two outgoing and at most two incoming edges of each color.
--
--   Differences from the source:
--   - encoding: $q$ a positive integer, $\mathbb Z_q^n$, indices $1,\dots,n$ → `[NeZero q]`, `Fin n → ZMod q`, indices `0, …, n−1`; reason: Lean convention; same instances
--   - reading: Construction 3.13: edges $u \xrightarrow{a} v$, $v \xrightarrow{-a} u$ for each row $a$ and $v-u=a$ → edge occurrences $(i,\sigma,u)$ (row, sign, tail) with head $u+\sigma a_i\in(\mathbb Z_q^n)_l$; parallel edges kept; reason: with repeated rows or $q=2$ a set of pairs would merge edges that the count $\theta^{(n,l,k)}$ of Eq. (7) and $|E| = m\theta$ count separately; for distinct rows and $q\ne 2$ the two readings coincide
--   - encoding: 'every edge $e=(u,v)$ has a reverse edge $e^{\mathrm{rev}}=(v,u)$', both colored $i$ → every edge occurrence `e` has an occurrence `e'` with swapped endpoints and the same color; reason: same property for edge occurrences
--   - encoding: 2-deficiency: at most 2 neighbours $w$ per color → at most 2 edge occurrences per color, out and in; reason: equal for simple digraphs; for the multigraph the occurrence count is the stronger property
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 17, Observation 4.11

import Mathlib
import Definitions.Def_SmallSecretLWE_Classical_Kikuchi

namespace SmallSecretLWE.Classical

/-- Observation 4.11. Let `A ∈ Z_q^{m×n}` have rows with exactly `k` nonzero entries and
`l ≥ k/2`. Every edge `e = (u, v)` of `K_l(A)` has a reverse edge `(v, u)` of the same color, and
the coloring by row index is 2-deficient. -/
theorem observation_4_11 {m n q : ℕ} [NeZero q] (k l : ℕ)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (hA : HasKSparseRows k A) (hl : (k : ℝ) / 2 ≤ l) :
    (∀ e : KEdge A l, ∃ e' : KEdge A l,
      (kikuchi A l).src e' = (kikuchi A l).tgt e ∧ (kikuchi A l).tgt e' = (kikuchi A l).src e ∧
        kColor e' = kColor e) ∧
    (kikuchi A l).IsDeficient kColor 2 := by sorry

end SmallSecretLWE.Classical
