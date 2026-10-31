-- Prove2me | Theorems.Thm_StreamSubmod_concavity
-- name    : StreamSubmod.concavity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:25.819982+00:00
-- url     : https://prove2.me/theorems/5d3e3aff-c22c-4635-85d7-b09650ad7cf8
-- title:
--   Concavity of $t\mapsto F((t\mathbf 1_S)\vee\mathbf 1_B)$ on $[0,1]$
-- statement:
--   Let $f:2^V\to\mathbb R$ be submodular with multilinear extension $F$, and let $S,B\subseteq V$. Then the function
--
--   $$
--   t\ \longmapsto\ F\bigl((t\cdot\mathbf 1_S)\vee\mathbf 1_B\bigr)
--   $$
--
--   is concave on $[0,1]$. Comparing the value at $t=b$ with the endpoints gives the bound $F((b\mathbf 1_S)\vee\mathbf 1_B)\ge(1-b)f(B)+b\,f(S\cup B)$ used in the proof of Lemma 6.
--
--   Differences from the source:
--   - generalization: S = Ŝi and B = OPT \ O → arbitrary sets S, B ⊆ V; reason: the sets of the page are a special case
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, proof of Lemma 6, p.9, "the submodularity of f implies that F((t·1_Ŝi)∨1_OPT\O) is a concave function of t within the range [0, 1]"

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Concavity (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, proof of Lemma 6, p.9): "the
submodularity of `f` implies that `F((t·𝟏_{Ŝᵢ}) ∨ 𝟏_{OPT\O})` is a concave function of `t` within the
range `[0, 1]`". Stated for arbitrary sets `S`, `B`. -/
theorem concavity {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf : Submodular f)
    (S B : Finset E) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t : ℝ => F f (fun e => max (t * (if e ∈ S then 1 else 0)) (if e ∈ B then 1 else 0))) := by sorry

end StreamSubmod
