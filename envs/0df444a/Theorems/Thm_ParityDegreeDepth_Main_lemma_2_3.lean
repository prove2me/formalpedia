-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_lemma_2_3
-- name    : ParityDegreeDepth.Main.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:51.746974+00:00
-- url     : https://prove2.me/theorems/c8ecce10-b384-4573-babb-e751577d2fab
-- title:
--   Lemma 2.3 — top finite-difference form
-- statement:
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ have exact algebraic normal-form degree $d\ge1$. The iterated difference $\Delta_{h_1}\cdots\Delta_{h_d}p(x)$ is independent of $x$. Its value $T(h_1,\ldots,h_d)$ is nonzero as a form, symmetric, multilinear, and zero whenever two arguments coincide. For distinct standard basis indices,
--   $$T(e_{i_1},\ldots,e_{i_d})=c_{\{i_1,\ldots,i_d\}},$$
--   where $c_S$ is the coefficient of $\prod_{i\in S}x_i$ in the unique multilinear normal form of $p$.
--
--   This identifies the top-degree coefficients with an intrinsic finite-difference tensor.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
--   - encoding: exact degree d, the top finite difference, and coefficient c_S → WithBot ℕ degree with zero at bottom, top difference evaluated at zero, and the published Boolean ANF coefficient transported to F₂; reason: basepoint independence is a conclusion, and false/true correspond to 0/1
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Lemma 2.3, PDF page 5 / printed page 4.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private def coefficient {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
  then 1 else 0

private def anfDegree {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) : WithBot ℕ :=
  Finset.univ.sup fun S : Finset (Fin n) =>
    if coefficient p S = 0 then ⊥ else (S.card : WithBot ℕ)

private def delta {n : ℕ} (h : Vec n (ZMod 2)) (p : Vec n (ZMod 2) → ZMod 2)
    (x : Vec n (ZMod 2)) : ZMod 2 := p (x + h) + p x

private def differences {n k : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (h : Fin k → Vec n (ZMod 2)) : Vec n (ZMod 2) → ZMod 2 :=
  (List.ofFn h).foldl (fun q v => delta v q) p

private abbrev Form (F : Type) (n d : ℕ) := (Fin d → Vec n F) → F

private def topForm {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (d : ℕ) : Form (ZMod 2) n d :=
  fun h => differences p h 0

private def IsMultilinear {F : Type} [Field F] {n d : ℕ} (T : Form F n d) : Prop :=
  (∀ x i u v, T (Function.update x i (u + v)) =
    T (Function.update x i u) + T (Function.update x i v)) ∧
  (∀ x i (c : F) u, T (Function.update x i (c • u)) = c * T (Function.update x i u))

private def IsSymmetric {F : Type} {n d : ℕ} (T : Form F n d) : Prop :=
  ∀ (σ : Equiv.Perm (Fin d)) x, T (x ∘ σ) = T x

private def IsAlternating {F : Type} [Zero F] {n d : ℕ} (T : Form F n d) : Prop :=
  ∀ x i j, i ≠ j → x i = x j → T x = 0


/-- lemma 2 3; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem lemma_2_3 {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hd : 1 ≤ d) (hp : anfDegree p = (d : WithBot ℕ)) :
    (∀ h x, differences p h x = topForm p d h) ∧
    (∃ h, topForm p d h ≠ 0) ∧
    IsSymmetric (topForm p d) ∧ IsMultilinear (topForm p d) ∧
    IsAlternating (topForm p d) ∧
    (∀ (indices : Fin d → Fin n), Function.Injective indices →
      topForm p d (fun i => Pi.single (indices i) 1) =
        coefficient p (Finset.univ.image indices)) := by sorry

end ParityDegreeDepth.Main
