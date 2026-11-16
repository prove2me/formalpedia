-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_lemma_5_9
-- name    : ParityBarrier563.Trilinear.Supplement.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:43:06.821335+00:00
-- url     : https://prove2.me/theorems/277b4340-467e-447d-9ece-f9676708ca1e
-- title:
--   Lemma 5.9 — Even moment of a restricted random shift of inverse trace
-- statement:
--   Let $n\ge1$ and choose any basis of $\mathbb F_{2^n}$. Let τ be a restriction of the n coordinates, σ a further restriction of live(τ), and $T=\operatorname{live}(\tau\sigma)$. Let $u\ge2$ be even and $J:\{0,1\}^T\to[-1,1]$. For $g=2I_e-1$, write $g^w(x)=g(x+w)$, where w is uniform in the span of the live(τ) basis vectors and zero elsewhere. Then
--   $$\mathbb E_w[(\mathbb E_z[g^w_{\tau\sigma}(z)J(z)])^u]\le u^{u/2}2^{-u|T|/2}+3u\,2^{n/2-|\operatorname{live}(\tau)|}.$$
--   This is an even-moment estimate for every bounded real test and every further restriction.
--
--   Differences from the source:
--   - encoding: uniform field shift on live coordinates and further restriction → uniform live cube, zeroFill, XOR and composed restriction; reason: these give precisely the source shift law and final live-coordinate domain
--   - encoding: the field of order 2^n in every binary basis → an arbitrary field K with an F₂-algebra structure and an n-vector basis; reason: the basis bijects K with F₂^n and enforces order 2^n without any additional restriction
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Lemma 5.9, printed p.23 / PDF p.25

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_InverseTrace

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Lemma 5.9: the shift is uniform on the live-coordinate subspace, zero elsewhere. -/
theorem lemma_5_9 (n : ℕ) (hn : 1 ≤ n)
    (K : Type) [Field K] [Algebra (ZMod 2) K]
    (e : Module.Basis (Fin n) (ZMod 2) K)
    (τ : Restriction (Fin n)) (σ : Restriction (Live τ))
    (u : ℕ) (hu : 2 ≤ u) (he : Even u)
    (J : RealFn (Live (compose τ σ))) (hJ : BoundedTest J) :
  avg (fun w => (avg (fun z =>
    restrict (compose τ σ) (shift (zeroFill τ w) (sgn (inverseTrace e))) z * J z)) ^ u) ≤
    (u : ℝ) ^ (u/2) * (2 : ℝ) ^ (-((u : ℝ) * Fintype.card (Live (compose τ σ)))/2) +
    3 * u * (2 : ℝ) ^ ((n : ℝ)/2 - Fintype.card (Live τ)) := by sorry

end ParityBarrier563.Trilinear.Supplement
