-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_lemma_5_8
-- name    : ParityBarrier563.Trilinear.Supplement.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:42:32.946828+00:00
-- url     : https://prove2.me/theorems/1ed4467f-7f61-46b5-9549-08e80ae221fd
-- title:
--   Lemma 5.8 — Products of inverse-trace shifts on every coordinate subcube
-- statement:
--   Let $n\ge1$, choose any $\mathbb F_2$-basis of $K=\mathbb F_{2^n}$, and let τ fix any subset of its n coordinates. For every nonempty finite set B⊆K, with y uniform among the extensions of τ,
--   $$\left|\mathbb E_y\prod_{v\in B}\chi((y+v)^{-1})\right|\le3|B|\,2^{n/2-|\operatorname{live}(\tau)|}.$$
--   Here χ is the absolute-trace character and inverse at zero is zero. This controls products of shifted inverse traces on every coordinate subcube.
--
--   Differences from the source:
--   - encoding: coordinate subcube and finite field → Fin n coordinates with a binary basis and a Finset B; reason: the basis identifies every field element with exactly one Boolean assignment
--   - encoding: the field of order 2^n in every binary basis → an arbitrary field K with an F₂-algebra structure and an n-vector basis; reason: the basis bijects K with F₂^n and enforces order 2^n without any additional restriction
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Lemma 5.8, printed p.22 / PDF p.24

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_InverseTrace

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Lemma 5.8, printed p.22 / PDF 24, including every coordinate subcube. -/
theorem lemma_5_8 (n : ℕ) (hn : 1 ≤ n)
    (K : Type) [Field K] [Algebra (ZMod 2) K]
    (e : Module.Basis (Fin n) (ZMod 2) K)
    (τ : Restriction (Fin n)) (B : Finset K) (hB : B.Nonempty) :
  |avg (fun z => ∏ v ∈ B, character n ((fieldPoint e (fill τ z) + v)⁻¹))| ≤
    3 * B.card * (2 : ℝ) ^ ((n : ℝ)/2 - Fintype.card (Live τ)) := by sorry

end ParityBarrier563.Trilinear.Supplement
