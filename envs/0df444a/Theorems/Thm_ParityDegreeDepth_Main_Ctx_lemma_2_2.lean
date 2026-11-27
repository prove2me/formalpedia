-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_Ctx_lemma_2_2
-- name    : ParityDegreeDepth.Main.Ctx.lemma_2_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:21:40.601638+00:00
-- url     : https://prove2.me/theorems/cbfbb973-f61e-5db9-8218-b3d9fd276cd9
-- title:
--   Lemma 2.2 over the public context: affine invariance of sparsity, spectral norm and parity depth
-- statement:
--   Let $f:\mathbb F_2^n\to\mathbb R$. For every injective linear coordinate map $B:\mathbb F_2^m\to\mathbb F_2^n$ and offset $a$, write $g(y)=f(a+By)$. Then
--   $$s(g)\le s(f),\qquad \|\widehat g\|_1\le\|\widehat f\|_1.$$
--   For every invertible affine change of coordinates, both inequalities are equalities. If $f$ is sign-valued, its minimum exact parity decision-tree depth is also unchanged.
--
--   This controls all affine restrictions, including points, without imposing a preferred basis.
--
--   **Formalization Note.** This is the mission milestone Lemma 2.2 with the identical Lean statement, but stated over the public shared context `Def_ParityDegreeDepth_Main_Context` (the definitions used by the paper's Supplement items) instead of private in-file copies, which match that context verbatim. A private `inductive ParityTree` in a statement can never be matched by the verifier, because a separately compiled solution cannot refer to another module's private inductive. Over the public context the statement is checkable.
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Lemma 2.2, PDF page 5 / printed page 4.

import Mathlib
import Definitions.Def_ParityDegreeDepth_Main_Context

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main.Ctx

open ParityDegreeDepth.Main

/-- Lemma 2.2 of Zhang, STOC 2027 submission #798, over the public context `Def_ParityDegreeDepth_Main_Context`. -/
theorem lemma_2_2 {n : ℕ} (f : Vec n (ZMod 2) → ℝ) :
    (∀ (m : ℕ) (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2))
      (a : Vec n (ZMod 2)), Function.Injective B →
      sparsity (f ∘ affineMap B a) ≤ sparsity f ∧
      spectralNorm (f ∘ affineMap B a) ≤ spectralNorm f) ∧
    (∀ (B : Vec n (ZMod 2) ≃ₗ[ZMod 2] Vec n (ZMod 2)) (a : Vec n (ZMod 2)),
      sparsity (fun x => f (a + B x)) = sparsity f ∧
      spectralNorm (fun x => f (a + B x)) = spectralNorm f ∧
      ((∀ x, f x = -1 ∨ f x = 1) →
        parityDepth (fun x => f (a + B x)) = parityDepth f)) := by sorry

end ParityDegreeDepth.Main.Ctx
