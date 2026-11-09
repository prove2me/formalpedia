-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_lemma_3_2
-- name    : TarskiBootstrap.Dimensional.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:13:41.080173+00:00
-- url     : https://prove2.me/theorems/8979a000-8f73-4160-a73b-57f819f7506f
-- title:
--   Lemma 3.2 — Antichain downward closure
-- statement:
--   Let $L$ be an arbitrary partially ordered set, $A\subseteq L$ an antichain, and $D=\{z:\exists a\in A,\ z\le a\}$. For $x<y$,
--
--   $$\bigl(x\in A\implies y\notin D\bigr)\quad\text{and}\quad\bigl(y\in A\implies x\in D\setminus A\bigr).$$
--
--   Both implications hold without a finiteness assumption on $L$ or $A$. They provide the order interface used by the chain constructor.
--
--   Differences from the source: none.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Lemma 3.2, PDF/printed pp. 11–12, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_DownwardClosure

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- Lemma 3.2, PDF/printed pp. 11–12: both implications, for arbitrary posets. -/
theorem lemma_3_2 {L : Type*} [PartialOrder L] (A : Set L)
    (hA : IsAntichain (· ≤ ·) A) {x y : L} (hxy : x < y) :
    (x ∈ A → y ∉ downwardClosure A) ∧
    (y ∈ A → x ∈ downwardClosure A \ A) := by sorry

end TarskiBootstrap.Dimensional
