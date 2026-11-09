-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_lemma_2_4
-- name    : ParityDegreeDepth.Main.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:45.334357+00:00
-- url     : https://prove2.me/theorems/8c57b1e0-8b4c-4bcf-ab33-ff80c3a28b40
-- title:
--   Lemma 2.4 — degree reduction on every coset
-- statement:
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ have degree $d\ge1$, and let $U\le\mathbb F_2^n$. Then
--   $$ (\Delta^d p)(U,\ldots,U)=0\quad\Longleftrightarrow\quad \deg(p|_{a+U})\le d-1\ \text{for every }a\in\mathbb F_2^n.$$
--   The restriction is expressed using every linear coordinate isomorphism onto $U$, including the zero-dimensional case.
--
--   The equivalence connects tensor vanishing to simultaneous degree reduction on all cosets.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
--   - encoding: degree of the restriction to every coset a + U → the degree bound for every linear isomorphism from a finite binary coordinate space onto U; reason: every finite-dimensional U admits such coordinates; every coset and basis is covered
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Lemma 2.4, PDF page 5 / printed page 4.

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

private def Vanishes {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (U : Submodule F (Vec n F)) : Prop := ∀ x, (∀ i, x i ∈ U) → T x = 0


/-- lemma 2 4; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem lemma_2_4 {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hd : 1 ≤ d) (hp : anfDegree p = (d : WithBot ℕ))
    (U : Submodule (ZMod 2) (Vec n (ZMod 2))) :
    Vanishes (topForm p d) U ↔
    ∀ (a : Vec n (ZMod 2)) (m : ℕ) (B : Vec m (ZMod 2) ≃ₗ[ZMod 2] U),
      anfDegree (fun y => p (a + (B y : Vec n (ZMod 2)))) ≤ ((d - 1 : ℕ) : WithBot ℕ) := by sorry

end ParityDegreeDepth.Main
