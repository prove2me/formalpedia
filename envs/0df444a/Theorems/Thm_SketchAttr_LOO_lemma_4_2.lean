-- Prove2me | Theorems.Thm_SketchAttr_LOO_lemma_4_2
-- name    : SketchAttr.LOO.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:29:33.96421+00:00
-- url     : https://prove2.me/theorems/7c33fd19-f86b-48f4-9f58-bf527838b1a6
-- title:
--   Lemma 4.2 — Gaussian tensor moments, both parts
-- statement:
--   Let $r\ge1$, let $S$ be a real symmetric order-$r$ tensor over $\mathbb R^n$, let $x\in\mathbb R^n$, and let $g\sim\mathrm{CN}(0,I_n)$. With $Y=S[g^{\otimes r}](g^\dagger x)^r/r!$, both parts of Lemma 4.2 assert
--   $$\mathbb E|S[g^{\otimes r}]|^2=r!\|S\|_F^2,\qquad\mathbb E|S[g^{\otimes r}]|^4\le(2r)!\|S\|_F^4,$$
--   $$\mathbb EY=S[x^{\otimes r}],\qquad\mathbb E|Y|^2\le\binom{2r}{r}\|S\|_F^2\|x\|_2^{2r}.$$
--   The conclusion also asserts integrability of every displayed integrand. These identities provide the sketch's value and variance control without imposing bounded Gaussian samples.
--
--   Differences from the source:
--   - encoding: real tensors and vectors with Gaussian expectations → complex-coordinate arrays with zero imaginary parts and Bochner integrals whose integrability is part of the conclusion; reason: the coordinate embedding changes no real tensor or vector and integrability prevents default-valued expectations
--   - encoding: positive integer input dimension n and indices in [n] → Fin n with an explicit hypothesis 1 <= n; reason: this records the positive-dimension convention in Section 3.1 and changes only the index base
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), pp. 10–11, Lemma 4.2; canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib
import Definitions.Def_SketchAttr_LOO_Sampling
open MeasureTheory

namespace SketchAttr.LOO

/-- Lemma 4.2, both parts, including existence of every displayed expectation. -/
theorem lemma_4_2 (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (T : Tensor n r)
    (hsym : T.IsSymmetric) (hreal : T.IsReal) (x : Vec n) (hx : ∀ i, (x i).im = 0) :
    Integrable (fun g => ‖diagonal T g‖ ^ 2) (gaussianVector n) ∧
    Integrable (fun g => ‖diagonal T g‖ ^ 4) (gaussianVector n) ∧
    Integrable (directionalSketch T x) (gaussianVector n) ∧
    Integrable (fun g => ‖directionalSketch T x g‖ ^ 2) (gaussianVector n) ∧
    (∫ g, ‖diagonal T g‖ ^ 2 ∂gaussianVector n) =
      (Nat.factorial r : ℝ) * frobNorm T ^ 2 ∧
    (∫ g, ‖diagonal T g‖ ^ 4 ∂gaussianVector n) ≤
      (Nat.factorial (2*r) : ℝ) * frobNorm T ^ 4 ∧
    (∫ g, directionalSketch T x g ∂gaussianVector n) = diagonal T x ∧
    (∫ g, ‖directionalSketch T x g‖ ^ 2 ∂gaussianVector n) ≤
      (Nat.choose (2*r) r : ℝ) * frobNorm T ^ 2 * ‖x‖ ^ (2*r) := by sorry

end SketchAttr.LOO
