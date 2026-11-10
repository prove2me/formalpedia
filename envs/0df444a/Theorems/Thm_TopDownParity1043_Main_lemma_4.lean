-- Prove2me | Theorems.Thm_TopDownParity1043_Main_lemma_4
-- name    : TopDownParity1043.Main.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:19:12.778557+00:00
-- url     : https://prove2.me/theorems/ca01fe1f-bcff-4d55-85ac-02c67098f687
-- title:
--   Lemma 4 — entropy deficit of a subcube fibre
-- statement:
--   Let $V$ be finite, let $X\subseteq\{0,1\}^V$ be nonempty, and let $S\subseteq V$. For a uniformly sampled $x\in X$, put $X_{x,S}=X\cap[x]_S$. Then
--   $$\mathbb E_{x\sim X}\left[|S|-\log_2|X_{x,S}|\right]\le |V|-\log_2|X|.$$
--
--   The deficit of the fibre is measured inside its $|S|$-dimensional cube, and the fibre contains the sampled point $x$. This relates the average conditional deficit to the original deficit and permits applying projection estimates inside subcubes.
--
--   Differences from the source:
--   - encoding: coordinates [n] → an arbitrary finite type V with Boolean words V → Bool; reason: every finite coordinate set is equivalent to Fin |V|, including every subcube coordinate subtype
--   - encoding: uniform x ∼ X → an explicit X.Nonempty assumption and the finite average divided by |X|; reason: a uniform law on X presupposes nonemptiness; every sampled fibre then contains its sample
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), Lemma 4, p. 7

import Mathlib
import Definitions.Def_TopDownParity1043_Main_Subcubes

set_option autoImplicit false
open scoped NNReal ENNReal

namespace TopDownParity1043.Main

/-- Lemma 4 (Entropy Lemma), p.7. The average is uniform on nonempty X.
For each sampled x the fibre contains x; its deficit uses dimension |S|. -/
theorem lemma_4 (V : Type) [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (hX : X.Nonempty) (S : Finset V) :
    uniformSetMean X (fun x => setDeficit S.card (fibre X x S)) ≤
      setDeficit (Fintype.card V) X := by sorry

end TopDownParity1043.Main
