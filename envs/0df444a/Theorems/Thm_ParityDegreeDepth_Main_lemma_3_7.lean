-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_lemma_3_7
-- name    : ParityDegreeDepth.Main.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:21.352398+00:00
-- url     : https://prove2.me/theorems/534b7ca6-e522-4cff-9aa4-dd9e4b3d33fd
-- title:
--   Lemma 3.7 — dimension-preserving binary descent
-- statement:
--   Let $T:(\mathbb F_2^n)^d\to\mathbb F_2$ be multilinear, with its original coefficients used for scalar extension. Let $K=\mathbb F_2(z_1,\ldots,z_L)$, and let $U\le K^n$ satisfy $\dim_K U=k$ and $T(K^n,U,\ldots,U)=0$. Then there is $U'\le\mathbb F_2^n$ with
--   $$\dim_{\mathbb F_2}U'=\dim_K U=k,\qquad T(\mathbb F_2^n,U',\ldots,U')=0,\qquad T(U',\ldots,U')=0.$$
--
--   The dimension is measured over each subspace's own coefficient field. This is descent with equal dimension and the complete one-free-slot identity, including $n=0$, $L=0$, or $k=0$.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
--   - encoding: a d-linear form with one free slot and d - 1 restricted slots → an explicit binder 1 ≤ d; reason: the one-free-slot expression presupposes positive arity; every source instance, including the d ≥ 3 applications, is retained
--   - encoding: extension using the same coefficients and dimensions over the respective fields → the standard-basis tensor coefficient formula and finrank over each subspace coefficient field; reason: a multilinear map is determined by those coefficients, and no dimension is taken over the wrong field
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Lemma 3.7, PDF page 10 / printed page 9.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private abbrev Form (F : Type) (n d : ℕ) := (Fin d → Vec n F) → F

private def IsMultilinear {F : Type} [Field F] {n d : ℕ} (T : Form F n d) : Prop :=
  (∀ x i u v, T (Function.update x i (u + v)) =
    T (Function.update x i u) + T (Function.update x i v)) ∧
  (∀ x i (c : F) u, T (Function.update x i (c • u)) = c * T (Function.update x i u))

private def Vanishes {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (U : Submodule F (Vec n F)) : Prop := ∀ x, (∀ i, x i ∈ U) → T x = 0

private def StrongVanishes {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (U : Submodule F (Vec n F)) : Prop :=
  ∀ (v : Vec n F) (u : Fin (d - 1) → U),
    T (fun i => if hi : i.val = 0 then v else (u ⟨i.val - 1, by omega⟩ : Vec n F)) = 0

private def extendForm {F E : Type} [Field F] [Field E] [Algebra F E] {n d : ℕ}
    (T : Form F n d) : Form E n d :=
  fun x => ∑ a : Fin d → Fin n,
    algebraMap F E (T (fun i => Pi.single (a i) 1)) * ∏ i, x i (a i)


/-- lemma 3 7; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem lemma_3_7 {n d L k : ℕ} (hd : 1 ≤ d) (T : Form (ZMod 2) n d)
    (hT : IsMultilinear T)
    (U : Submodule (FractionRing (MvPolynomial (Fin L) (ZMod 2)))
      (Vec n (FractionRing (MvPolynomial (Fin L) (ZMod 2)))))
    (hk : Module.finrank (FractionRing (MvPolynomial (Fin L) (ZMod 2))) U = k)
    (hU : StrongVanishes (extendForm (E := FractionRing (MvPolynomial (Fin L) (ZMod 2))) T) U) :
    ∃ U' : Submodule (ZMod 2) (Vec n (ZMod 2)),
      Module.finrank (ZMod 2) U' = Module.finrank (FractionRing (MvPolynomial (Fin L) (ZMod 2))) U ∧
      Module.finrank (ZMod 2) U' = k ∧ StrongVanishes T U' ∧ Vanishes T U' := by sorry

end ParityDegreeDepth.Main
