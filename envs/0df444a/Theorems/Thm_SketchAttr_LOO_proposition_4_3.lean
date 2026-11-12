-- Prove2me | Theorems.Thm_SketchAttr_LOO_proposition_4_3
-- name    : SketchAttr.LOO.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:28:27.936212+00:00
-- url     : https://prove2.me/theorems/a216d7f0-cc7e-41d6-87c3-4e832ab2d23d
-- title:
--   Proposition 4.3 — value and gradient circuit of linear size
-- statement:
--   There is a universal constant $C>0$ such that every scalar arithmetic circuit $f$ with $n$ inputs admits an arithmetic circuit $b$ with $n+1$ outputs satisfying
--   $$\operatorname{size}(b)\le C\operatorname{size}(f),\qquad b(w)=(f(w),\nabla f(w))\quad(w\in\mathbb C^n).$$
--   The gradient is holomorphic: its $i$th coordinate is $Df(w)[e_i]$ over $\mathbb C$. This supplies the circuit object used by the backward–forward sketches, with one constant for all circuits and all input dimensions.
--
--   Differences from the source:
--   - encoding: an arithmetic circuit of size O(size(f)) computing the value-gradient pair → one positive constant quantified before all circuits and coordinatewise equality in n+1 outputs; reason: this expands the uniform O notation without weakening its size guarantee
--   - encoding: positive integer input dimension n and indices in [n] → Fin n with an explicit hypothesis 1 <= n; reason: this records the positive-dimension convention in Section 3.1 and changes only the index base
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), p. 11, Proposition 4.3 (citing [RHW86] and [CKW11, Theorem 9.10]); canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib
import Definitions.Def_SketchAttr_LOO_Taylor

namespace SketchAttr.LOO

/-- Proposition 4.3: a constant-size-overhead circuit for value and gradient. -/
theorem proposition_4_3 : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ c : Circuit n 1,
    ∃ b : Circuit n (n+1), (b.size : ℝ) ≤ C * c.size ∧
      ∀ w : Vec n, b.eval (fun i => w i) 0 = circuitFunction c w ∧
        ∀ i : Fin n, b.eval (fun j => w j) i.succ = gradient (circuitFunction c) w i := by sorry

end SketchAttr.LOO
