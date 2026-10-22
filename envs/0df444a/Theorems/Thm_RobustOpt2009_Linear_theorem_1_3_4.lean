-- Prove2me | Theorems.Thm_RobustOpt2009_Linear_theorem_1_3_4
-- name    : RobustOpt2009.Linear.theorem_1_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:42:28.235623+00:00
-- url     : https://prove2.me/theorems/06ad878c-8c2f-4c96-b68e-00295e92ded4
-- title:
--   Theorem 1.3.4 — conic dual certificate
-- statement:
--   Let $K\subseteq\mathbb R^N$ be a closed, convex, pointed cone with nonempty interior, and let the nonempty perturbation set be
--   $$ Z=\{z\in\mathbb R^L:\exists v\in\mathbb R^u,\ Pz+Qv+p\in K\}. $$
--   Assume either that $K$ is polyhedral or that some $\bar z,\bar v$ satisfy $P\bar z+Q\bar v+p\in\operatorname{int}K$. For every $x\in\mathbb R^n$, the original uncertain inequality holds for every $z\in Z$ if and only if there exists $y\in\mathbb R^N$ such that
--   $$ p^Ty+(a^0)^Tx\le b^0,\quad Q^Ty=0,\quad (P^Ty)_\ell+(a^\ell)^Tx=b^\ell\ (1\le\ell\le L),\quad y\in K^*. $$
--   Here $K^*=\{y:y^Tz\ge0\text{ for every }z\in K\}$. This states the projection equivalence in (1.3.12).
--
--   **Formalization Note** Nonemptiness is the uncertainty-set convention made explicit in the chapter brief and Corollary 1.3.5. The imported good-cone and dual-cone definitions are used without the separate full-column-rank assumption in their original development. No attainment of the worst-case perturbation is assumed.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Theorem 1.3.4, printed pp. 20–21 (PDF pp. 46–47)

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

theorem theorem_1_3_4 {n L u N : ℕ} (D : Data n L) (R : Lift (Fin N) L u)
    (K : Set (Fin N → ℝ)) (hK : ModernConvex.ConicDuality.IsGoodCone K)
    (hne : (R.set K).Nonempty)
    (hqual : Polyhedral K ∨ ∃ z v, R.value z v ∈ interior K) :
    ∀ x, Robust D (R.set K) x ↔
      ∃ y, Certificate D R (ModernConvex.ConicDuality.dualCone K) x y := by sorry

end RobustOpt2009.Linear
