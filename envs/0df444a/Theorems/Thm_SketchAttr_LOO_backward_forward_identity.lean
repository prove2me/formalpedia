-- Prove2me | Theorems.Thm_SketchAttr_LOO_backward_forward_identity
-- name    : SketchAttr.LOO.backward_forward_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:28:27.418377+00:00
-- url     : https://prove2.me/theorems/e21089fa-c86b-40c2-b827-bf5f04c6d01f
-- title:
--   Section 4.2, p. 12 — backward–forward coefficient identity
-- statement:
--   Let $f:\mathbb C^n\to\mathbb C$ be a scalar arithmetic circuit, $g\in\mathbb C^n$, and $1\le r\le N$ with $N\ge1$. The normalized coefficient of the gradient along the line $zg$ is
--   $$c_r(g)=\frac1r[z^{r-1}]\nabla f(zg)=T_f^{(r)}[\cdot,g^{\otimes(r-1)}].$$
--   The equality is coordinatewise for every input coordinate. It identifies the object returned by differentiation with the tensor contraction used in the statistical estimates; it does not assume a circuit-size or machine-time bound.
--
--   Differences from the source:
--   - encoding: coefficient extraction from the polynomial gradient along zg → coefficient represented by its normalized directional derivative of order r-1 at zero; reason: these are the same coefficient for every circuit polynomial and r is explicitly positive
--   - encoding: positive integer input dimension n and indices in [n] → Fin n with an explicit hypothesis 1 <= n; reason: this records the positive-dimension convention in Section 3.1 and changes only the index base
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), p. 12, Section 4.2 displayed identity; canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib
import Definitions.Def_SketchAttr_LOO_Taylor

namespace SketchAttr.LOO

/-- Section 4.2, p.12: the normalized coefficients computed by a sketch. -/
theorem backward_forward_identity (n : ℕ) (hn : 1 ≤ n) (c : Circuit n 1) (N : ℕ) (hN : 1 ≤ N)
    (g : Vec n) (r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N) (i : Fin n) :
    sketchCoeff (circuitFunction c) r g i =
      diagonal (slice (taylorTensor (circuitFunction c) r) i) g := by sorry

end SketchAttr.LOO
