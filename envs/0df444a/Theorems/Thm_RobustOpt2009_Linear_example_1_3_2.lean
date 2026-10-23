-- Prove2me | Theorems.Thm_RobustOpt2009_Linear_example_1_3_2
-- name    : RobustOpt2009.Linear.example_1_3_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:42:22.614606+00:00
-- url     : https://prove2.me/theorems/bd6f1ca1-2ddf-46cd-ba77-eabedf852772
-- title:
--   Example 1.3.2 — interval uncertainty
-- statement:
--   For arbitrary affine coefficients $a^0,b^0,a^\ell,b^\ell$ and a decision vector $x\in\mathbb R^n$, the uncertain linear inequality holds for every $z\in[-1,1]^L$ if and only if
--   $$ (a^0)^Tx+\sum_{\ell=1}^L|(a^\ell)^Tx-b^\ell|\le b^0. $$
--   This inequality is in turn equivalent to the existence of $v\in\mathbb R^L$ satisfying
--   $$ -v_\ell\le (a^\ell)^Tx-b^\ell\le v_\ell\ (1\le\ell\le L),\qquad (a^0)^Tx+\sum_\ell v_\ell\le b^0. $$
--   This gives both representations (1.3.7) and (1.3.8).
--
--   **Formalization Note** The box is specified coordinatewise. Indices use zero-based finite types, and empty coordinate lists have their usual empty-sum meaning.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Example 1.3.2, equations (1.3.7)–(1.3.8), printed p. 19 (PDF p. 45)

import Definitions.Def_RobustOpt2009_Linear_Model

open Matrix
open scoped BigOperators

/- Imported dependency declarations (code snapshot for the blind auditor).
open Matrix

namespace ModernConvex.ConicDuality


def IsConvexCone {m : ℕ} (K : Set (Fin m → ℝ)) : Prop :=
  K.Nonempty ∧ (∀ a ∈ K, ∀ a' ∈ K, a + a' ∈ K) ∧ (∀ a ∈ K, ∀ t : ℝ, 0 ≤ t → t • a ∈ K)


def IsPointedSet {m : ℕ} (K : Set (Fin m → ℝ)) : Prop :=
  ∀ a : Fin m → ℝ, a ∈ K → -a ∈ K → a = 0


def IsGoodCone {m : ℕ} (K : Set (Fin m → ℝ)) : Prop :=
  IsConvexCone K ∧ IsPointedSet K ∧ IsClosed K ∧ (interior K).Nonempty


def dualCone {m : ℕ} (K : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {l | ∀ a ∈ K, 0 ≤ l ⬝ᵥ a}


end ModernConvex.ConicDuality

open Matrix
open scoped BigOperators

namespace RobustOpt2009.Linear


structure Data (n L : ℕ) where
  a0 : Fin n → ℝ
  b0 : ℝ
  a : Fin L → Fin n → ℝ
  b : Fin L → ℝ


def Robust {n L : ℕ} (D : Data n L) (Z : Set (Fin L → ℝ)) (x : Fin n → ℝ) : Prop :=
  ∀ z ∈ Z, D.a0 ⬝ᵥ x + ∑ l, z l * (D.a l ⬝ᵥ x) ≤ D.b0 + ∑ l, z l * D.b l


structure Lift (ι : Type) (L u : ℕ) where
  P : Fin L → ι → ℝ
  Q : Fin u → ι → ℝ
  p : ι → ℝ

def Lift.value {ι : Type} {L u : ℕ} (R : Lift ι L u)
    (z : Fin L → ℝ) (v : Fin u → ℝ) : ι → ℝ :=
  fun i => (∑ l, z l * R.P l i) + (∑ j, v j * R.Q j i) + R.p i

def Lift.set {ι : Type} {L u : ℕ} (R : Lift ι L u) (K : Set (ι → ℝ)) : Set (Fin L → ℝ) :=
  {z | ∃ v, R.value z v ∈ K}


def Polyhedral {N : ℕ} (K : Set (Fin N → ℝ)) : Prop :=
  ∃ m : ℕ, ∃ A : Fin m → Fin N → ℝ, K = {z | ∀ j, 0 ≤ A j ⬝ᵥ z}


def Certificate {ι : Type} [Fintype ι] {n L u : ℕ} (D : Data n L)
    (R : Lift ι L u) (C : Set (ι → ℝ)) (x : Fin n → ℝ) (y : ι → ℝ) : Prop :=
  R.p ⬝ᵥ y + D.a0 ⬝ᵥ x ≤ D.b0 ∧
  (∀ j, R.Q j ⬝ᵥ y = 0) ∧
  (∀ l, R.P l ⬝ᵥ y + D.a l ⬝ᵥ x = D.b l) ∧ y ∈ C


inductive ConeShape where
  | orthant (N : ℕ)
  | lorentz (m : ℕ) (d : Fin m → ℕ)
  | psd (k : ℕ)

def ConeShape.Index : ConeShape → Type
  | .orthant N => Fin N
  | .lorentz m d => (s : Fin m) × Option (Fin (d s))
  | .psd k => Fin k × Fin k

instance (s : ConeShape) : Fintype s.Index := by
  cases s <;> dsimp [ConeShape.Index] <;> infer_instance


def ConeShape.cone : (s : ConeShape) → Set (s.Index → ℝ)
  | .orthant _ => {y | ∀ i, 0 ≤ y i}
  | .lorentz _ _ => {y | ∀ s, Real.sqrt (∑ j, (y ⟨s, some j⟩) ^ 2) ≤ y ⟨s, none⟩}
  | .psd _ => {y | Matrix.PosSemidef (fun i j => y (i,j))}


def ConeShape.strictCone : (s : ConeShape) → Set (s.Index → ℝ)
  | .orthant _ => {y | ∀ i, 0 < y i}
  | .lorentz _ _ => {y | ∀ s, Real.sqrt (∑ j, (y ⟨s, some j⟩) ^ 2) < y ⟨s, none⟩}
  | .psd _ => {y | Matrix.PosDef (fun i j => y (i,j))}


def ConeShape.ambient : (s : ConeShape) → Set (s.Index → ℝ)
  | .orthant _ => Set.univ
  | .lorentz _ _ => Set.univ
  | .psd _ => {y | ∀ i j, y (i,j) = y (j,i)}

def WellFormed {L u : ℕ} (s : ConeShape) (R : Lift s.Index L u) : Prop :=
  R.p ∈ s.ambient ∧ (∀ l, R.P l ∈ s.ambient) ∧ (∀ j, R.Q j ∈ s.ambient)


def Qualified {L u : ℕ} : (s : ConeShape) → Lift s.Index L u → Prop
  | .orthant _, _ => True
  | (.lorentz m d), R => ∃ z v, R.value z v ∈ (ConeShape.lorentz m d).strictCone
  | (.psd k), R => ∃ z v, R.value z v ∈ (ConeShape.psd k).strictCone


structure ExplicitSystem (ι : Type) (n e : ℕ) where
  scalarX : Fin n → ℝ
  scalarY : ι → ℝ
  scalarRhs : ℝ
  eqX : Fin e → Fin n → ℝ
  eqY : Fin e → ι → ℝ
  eqRhs : Fin e → ℝ
  cone : Set (ι → ℝ)

def ExplicitSystem.Feasible {ι : Type} [Fintype ι] {n e : ℕ}
    (S : ExplicitSystem ι n e) (x : Fin n → ℝ) (y : ι → ℝ) : Prop :=
  S.scalarX ⬝ᵥ x + S.scalarY ⬝ᵥ y ≤ S.scalarRhs ∧
  (∀ j, S.eqX j ⬝ᵥ x + S.eqY j ⬝ᵥ y = S.eqRhs j) ∧ y ∈ S.cone


def reformulation {ι : Type} {n L u : ℕ} (D : Data n L) (R : Lift ι L u)
    (C : Set (ι → ℝ)) : ExplicitSystem ι n (u + L) where
  scalarX := D.a0
  scalarY := R.p
  scalarRhs := D.b0
  eqX := Fin.addCases (fun _ => 0) D.a
  eqY := Fin.addCases R.Q R.P
  eqRhs := Fin.addCases (fun _ => 0) D.b
  cone := C


def ExplicitSystem.coefficientCount {ι : Type} [Fintype ι] {n e : ℕ}
    (_S : ExplicitSystem ι n e) : ℕ := (e + 1) * (n + Fintype.card ι + 1)


def ConeShape.coneSize : ConeShape → ℕ
  | .orthant N => N
  | .lorentz m d => ∑ s : Fin m, (d s + 1)
  | .psd k => k * k


def inputSize {n L u : ℕ} (s : ConeShape) (_D : Data n L) (_R : Lift s.Index L u) : ℕ :=
  1 + n + L + u + Fintype.card s.Index +
  (L + 1) * (n + 1) + (L + u + 1) * Fintype.card s.Index + s.coneSize


def outputSize {n L u : ℕ} (s : ConeShape) (D : Data n L) (R : Lift s.Index L u) : ℕ :=
  n + Fintype.card s.Index + (reformulation D R s.cone).coefficientCount + s.coneSize

end RobustOpt2009.Linear
-/

namespace RobustOpt2009.Linear

theorem example_1_3_2 {n L : ℕ} (D : Data n L) (x : Fin n → ℝ) :
    (Robust D {z | ∀ l, |z l| ≤ 1} x ↔
      D.a0 ⬝ᵥ x + ∑ l, |D.a l ⬝ᵥ x - D.b l| ≤ D.b0) ∧
    (D.a0 ⬝ᵥ x + ∑ l, |D.a l ⬝ᵥ x - D.b l| ≤ D.b0 ↔
      ∃ v : Fin L → ℝ, (∀ l, -v l ≤ D.a l ⬝ᵥ x - D.b l ∧
        D.a l ⬝ᵥ x - D.b l ≤ v l) ∧ D.a0 ⬝ᵥ x + ∑ l, v l ≤ D.b0) := by sorry

end RobustOpt2009.Linear
