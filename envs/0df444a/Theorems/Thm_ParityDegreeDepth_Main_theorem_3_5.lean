-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_theorem_3_5
-- name    : ParityDegreeDepth.Main.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:52.514892+00:00
-- url     : https://prove2.me/theorems/50671668-9bc3-4c61-86a0-1aa7c36e9b3b
-- title:
--   Theorem 3.5 — strong generic radical vanishing
-- statement:
--   Let $\mathbb F$ be any field, let $d\ge3$, and let $T:(\mathbb F^n)^d\to\mathbb F$ be a symmetric multilinear form. For independent formal anchor blocks $t_1,\ldots,t_{d-2}$, set $K=\mathbb F(t_1,\ldots,t_{d-2})$, $A=T(t_1,\ldots,t_{d-2},-,-)$, $R=\operatorname{rank}_K A$, and $U=\ker A$. Then
--   $$\dim_K U=n-R,\qquad T(K^n,U,\ldots,U)=0.$$
--   The second equality means that one argument is arbitrary in $K^n$ and the other $d-1$ arguments belong to $U$. Scalar extension uses the original coefficients of $T$.
--
--   This asserts the strong radical identity over every field; no alternating or characteristic-two assumption is imposed.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
--   - encoding: a symmetric multilinear form, its generic contraction A, rank R and radical U → an explicit multilinearity predicate, coefficient-wise scalar extension, the standard Gram matrix and its kernel; reason: no desired vanishing property is bundled into U, and matrix rank and kernel agree with the bilinear definitions for symmetric A
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Theorem 3.5, PDF page 7 / printed page 6 (continues PDF 8 / printed 7).

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

private def IsSymmetric {F : Type} {n d : ℕ} (T : Form F n d) : Prop :=
  ∀ (σ : Equiv.Perm (Fin d)) x, T (x ∘ σ) = T x

private def StrongVanishes {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (U : Submodule F (Vec n F)) : Prop :=
  ∀ (v : Vec n F) (u : Fin (d - 1) → U),
    T (fun i => if hi : i.val = 0 then v else (u ⟨i.val - 1, by omega⟩ : Vec n F)) = 0

private def extendForm {F E : Type} [Field F] [Field E] [Algebra F E] {n d : ℕ}
    (T : Form F n d) : Form E n d :=
  fun x => ∑ a : Fin d → Fin n,
    algebraMap F E (T (fun i => Pi.single (a i) 1)) * ∏ i, x i (a i)

private abbrev AnchorRing (F : Type) [CommRing F] (n k : ℕ) := MvPolynomial (Fin k × Fin n) F

private abbrev AnchorField (F : Type) [Field F] (n k : ℕ) := FractionRing (AnchorRing F n k)

private def genericMatrix {F : Type} [Field F] {n d : ℕ} (T : Form F n d) :
    Matrix (Fin n) (Fin n) (AnchorRing F n (d - 2)) :=
  fun i j => ∑ a : Fin (d - 2) → Fin n,
    MvPolynomial.C (T (fun s => if hs : s.val < d - 2 then Pi.single (a ⟨s.val, hs⟩) 1
      else if s.val = d - 2 then Pi.single i 1 else Pi.single j 1)) *
    ∏ t, MvPolynomial.X (t, a t)

private def genericContraction {F : Type} [Field F] {n d : ℕ} (T : Form F n d) :
    Matrix (Fin n) (Fin n) (AnchorField F n (d - 2)) :=
  (genericMatrix T).map (algebraMap (AnchorRing F n (d - 2)) (AnchorField F n (d - 2)))

private def genericRank {F : Type} [Field F] {n d : ℕ} (T : Form F n d) : ℕ :=
  (genericContraction T).rank

private def genericRadical {F : Type} [Field F] {n d : ℕ} (T : Form F n d) :
    Submodule (AnchorField F n (d - 2)) (Vec n (AnchorField F n (d - 2))) :=
  LinearMap.ker (Matrix.mulVecLin (genericContraction T))


/-- theorem 3 5; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem theorem_3_5 {F : Type} [Field F] {n d : ℕ} (hd : 3 ≤ d)
    (T : Form F n d) (hT : IsMultilinear T) (hs : IsSymmetric T) :
    Module.finrank (AnchorField F n (d - 2)) (genericRadical T) = n - genericRank T ∧
    StrongVanishes (extendForm (E := AnchorField F n (d - 2)) T) (genericRadical T) := by sorry

end ParityDegreeDepth.Main
