-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_Ctx_lemma_2_6
-- name    : ParityDegreeDepth.Main.Ctx.lemma_2_6
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:21:36.381686+00:00
-- url     : https://prove2.me/theorems/04d3a472-0735-5520-b80e-368e46b19f63
-- title:
--   Lemma 2.6 over the public context: quadratic phases
-- statement:
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ have degree at most two and let its polar form $\beta_p(u,v)=p(u+v)+p(u)+p(v)+p(0)$ have rank $2r$. For $f=(-1)^p$,
--   $$s(f)=2^{2r},\qquad |\widehat f(\xi)|\in\{0,2^{-r}\}\ \text{for every }\xi,\qquad\|\widehat f\|_1=2^r,\qquad D_\oplus(f)\le r+1.$$
--
--   This supplies both the complete flat-spectrum statement and the terminal tree bound, including polar rank zero.
--
--   **Formalization Note.** This is the mission milestone Lemma 2.6 with the identical Lean statement, but stated over the public shared context `Def_ParityDegreeDepth_Main_Context` (the definitions used by the paper's Supplement items) instead of private in-file copies, which match that context verbatim. A private `inductive ParityTree` in a statement can never be matched by the verifier, because a separately compiled solution cannot refer to another module's private inductive. Over the public context the statement is checkable.
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Lemma 2.6, PDF page 6 / printed page 5.

import Mathlib
import Definitions.Def_ParityDegreeDepth_Main_Context

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main.Ctx

open ParityDegreeDepth.Main

/-- Lemma 2.6 of Zhang, STOC 2027 submission #798, over the public context `Def_ParityDegreeDepth_Main_Context`. -/
theorem lemma_2_6 {n r : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hp : anfDegree p ≤ (2 : WithBot ℕ))
    (hr : (contraction (topForm p 2) (fun i => Fin.elim0 i)).rank = 2 * r) :
    sparsity (phase p) = 2 ^ (2 * r) ∧
    (∀ ξ, |QAlgorithms.boolFourier (phase p) ξ| = 0 ∨
      |QAlgorithms.boolFourier (phase p) ξ| = (2 : ℝ) ^ (-(r : ℤ))) ∧
    spectralNorm (phase p) = (2 : ℝ) ^ r ∧ parityDepth (phase p) ≤ r + 1 := by sorry

end ParityDegreeDepth.Main.Ctx
