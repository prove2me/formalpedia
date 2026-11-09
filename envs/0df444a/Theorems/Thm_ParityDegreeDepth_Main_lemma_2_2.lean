-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_lemma_2_2
-- name    : ParityDegreeDepth.Main.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:39.10788+00:00
-- url     : https://prove2.me/theorems/83007e3d-7e9f-4311-a452-93f2facbcc2d
-- title:
--   Lemma 2.2 — affine restriction
-- statement:
--   Let $f:\mathbb F_2^n\to\mathbb R$. For every injective linear coordinate map $B:\mathbb F_2^m\to\mathbb F_2^n$ and offset $a$, write $g(y)=f(a+By)$. Then
--   $$s(g)\le s(f),\qquad \|\widehat g\|_1\le\|\widehat f\|_1.$$
--   For every invertible affine change of coordinates, both inequalities are equalities. If $f$ is sign-valued, its minimum exact parity decision-tree depth is also unchanged.
--
--   This controls all affine restrictions, including points, without imposing a preferred basis.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
--   - encoding: affine subspaces in affine coordinates → all injective linear coordinate maps with offsets, and all invertible linear maps with offsets; reason: each image is exactly the corresponding affine subspace, and every choice of affine coordinates occurs
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Lemma 2.2, PDF page 5 / printed page 4.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private def spectralNorm {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℝ :=
  ∑ a, |QAlgorithms.boolFourier f a|

private def sparsity {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℕ :=
  (Finset.univ.filter fun a => QAlgorithms.boolFourier f a ≠ 0).card

private def affineMap {m n : ℕ} (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2))
    (a : Vec n (ZMod 2)) (y : Vec m (ZMod 2)) : Vec n (ZMod 2) := a + B y

private inductive ParityTree (n : ℕ) where
  | leaf (b : Bool)
  | query (a : Vec n (ZMod 2)) (ha : a ≠ 0) (zero one : ParityTree n)

private def treeDepth {n : ℕ} : ParityTree n → ℕ
  | .leaf _ => 0
  | .query _ _ l r => 1 + max (treeDepth l) (treeDepth r)

private def treeEval {n : ℕ} : ParityTree n → Vec n (ZMod 2) → ℝ
  | .leaf b, _ => if b then -1 else 1
  | .query a _ l r, x => if ∑ i, a i * x i = 0 then treeEval l x else treeEval r x

private def parityDepth {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℕ :=
  sInf {k | ∃ t : ParityTree n, treeDepth t = k ∧ ∀ x, treeEval t x = f x}


/-- lemma 2 2; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
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

end ParityDegreeDepth.Main
