-- Prove2me | Theorems.Thm_RobustOpt2009_CQApproximation_least_squares_sdp
-- name    : RobustOpt2009.CQApproximation.least_squares_sdp
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:44:05.989839+00:00
-- url     : https://prove2.me/theorems/a68bba8e-d87c-4a01-b416-af5346037b5d
-- title:
--   Theorem 7.1.2 — SDP approximation of structured robust least squares
-- statement:
--   Let the real least-squares constraint have the structured norm-bounded uncertainty of (7.1.1)–(7.1.3), with positive residual dimension, a positive number $N$ of blocks, affine factors of which at least one in each block is constant and nonzero, and neither factor identically zero. Normalize scalar blocks to $1\times1$ as in Remark 7.1.1. For every uncertainty radius $\rho>0$ and the same decision and threshold $(y,\tau)$, let $S_\rho(y,\tau)$ denote extendibility to the explicit LMI system (7.1.11), and $R_\rho(y,\tau)$ denote robust feasibility of the original norm inequality. Then
--   $$S_\rho(y,\tau)\Longrightarrow R_\rho(y,\tau),$$
--   $$\neg S_\rho(y,\tau)\Longrightarrow\neg R_{(\pi/2)\rho}(y,\tau),$$
--   and if $N=1$,
--   $$S_\rho(y,\tau)\Longleftrightarrow R_\rho(y,\tau).$$
--   Thus the explicit semidefinite approximation is safe, has tightness factor at most $\pi/2$, and is exact for one block.
--
--   **Formalization Note** Robust feasibility quantifies over the original vector residual, not a certificate. Both orientations of the affine factors are constructed in the definition. Tightness changes only the uncertainty radius and keeps $y,\tau$ fixed; it is not an objective-value ratio. Tractability is represented by the explicit finite system of affine matrix inequalities, without a separate bit-complexity model.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Theorem 7.1.2 and (7.1.11), printed pp. 182–183 (PDF pp. 208–209), with standing hypotheses on printed pp. 179–181 (PDF pp. 205–207).

import Definitions.Def_RobustOpt2009_CQApproximation_LeastSquares

/-
BEGIN IMPORTED LEAN SOURCE SNAPSHOT
FILE: Def_RobustOpt2009_CQApproximation_Basic.lean
import Mathlib

open Matrix
open scoped BigOperators

namespace RobustOpt2009.CQApproximation

/-- Euclidean operator-norm bound, written without choosing a matrix norm instance. -/
def OperatorBound {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (r : ℝ) : Prop :=
  ∀ v : Fin q → ℝ,
    ‖(WithLp.toLp 2 (M *ᵥ v) : EuclideanSpace ℝ (Fin p))‖ ≤
      r * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin q))‖

/-- Scalar coordinate first, followed by the residual coordinates. -/
def arrow {k : ℕ} (u : Fin k → ℝ) (t : ℝ) :
    Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ :=
  Matrix.fromBlocks (fun _ _ => t) (fun _ j => u j) (fun i _ => u i)
    (t • (1 : Matrix (Fin k) (Fin k) ℝ))

/-- The symmetric contribution of a full matrix perturbation. -/
def blockTerm {m p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (R : Matrix (Fin q) (Fin m) ℝ) (η : Matrix (Fin p) (Fin q) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  L.transpose * η * R + R.transpose * η.transpose * L

end RobustOpt2009.CQApproximation

FILE: Def_RobustOpt2009_CQApproximation_LeastSquares.lean
import Definitions.Def_RobustOpt2009_CQApproximation_Basic

open Matrix
open scoped BigOperators

namespace RobustOpt2009.CQApproximation

/-- The two orientations in (7.1.5). In the second constructor η is the transpose
of the original perturbation: the fixed factor always has p rows. -/
inductive LSBlock (d k p q : ℕ) where
  | leftFixed (L : Matrix (Fin p) (Fin k) ℝ)
      (R : (Fin d → ℝ) →ᵃ[ℝ] (Fin q → ℝ))
  | rightFixed (L : Fin p → ℝ)
      (R : (Fin d → ℝ) →ᵃ[ℝ] Matrix (Fin q) (Fin k) ℝ)

/-- The constant factor in the arrow representation, constructed from original data. -/
def LSBlock.hatL {d k p q : ℕ} (b : LSBlock d k p q) :
    Matrix (Fin p) (Unit ⊕ Fin k) ℝ :=
  match b with
  | .leftFixed L _ => fun i j => Sum.elim (fun _ => 0) (L i) j
  | .rightFixed L _ => fun i j => Sum.elim (fun _ => L i) (fun _ => 0) j

/-- The affine factor in the arrow representation. -/
def LSBlock.hatR {d k p q : ℕ} (b : LSBlock d k p q) (y : Fin d → ℝ) :
    Matrix (Fin q) (Unit ⊕ Fin k) ℝ :=
  match b with
  | .leftFixed _ R => fun i j => Sum.elim (fun _ => R y i) (fun _ => 0) j
  | .rightFixed _ R => fun i j => Sum.elim (fun _ => 0) (R y i) j

/-- Original vector perturbation L(y)ᵀ η R(y), with transposition when the right
factor is constant. -/
def LSBlock.effect {d k p q : ℕ} (b : LSBlock d k p q) (y : Fin d → ℝ)
    (η : Matrix (Fin p) (Fin q) ℝ) : Fin k → ℝ :=
  match b with
  | .leftFixed L R => L.transpose *ᵥ (η *ᵥ R y)
  | .rightFixed L R => (R y).transpose *ᵥ (η.transpose *ᵥ L)

/-- Neither factor is identically zero, as in (7.1.2); the affine factor may vanish
at particular decisions. -/
def LSBlock.Nonzero {d k p q : ℕ} (b : LSBlock d k p q) : Prop :=
  match b with
  | .leftFixed L R => L ≠ 0 ∧ ∃ y, R y ≠ 0
  | .rightFixed L R => L ≠ 0 ∧ ∃ y, R y ≠ 0

/-- Structured real least-squares data after the source's scalar-block normalization. -/
structure LSData (d k N : ℕ) where
  p : Fin N → ℕ
  q : Fin N → ℕ
  p_pos : ∀ i, 0 < p i
  q_pos : ∀ i, 0 < q i
  scalar : Finset (Fin N)
  scalar_size : ∀ i ∈ scalar, p i = 1 ∧ q i = 1
  block : ∀ i, LSBlock d k (p i) (q i)
  nonzero : ∀ i, (block i).Nonzero
  nominal : (Fin d → ℝ) →ᵃ[ℝ] (Fin k → ℝ)

/-- Independent operator-norm balls; scalar blocks are 1 by 1, so their scalar
restriction is automatic. -/
def LSData.Admissible {d k N : ℕ} (D : LSData d k N) (ρ : ℝ)
    (η : ∀ i, Matrix (Fin (D.p i)) (Fin (D.q i)) ℝ) : Prop :=
  ∀ i, OperatorBound (η i) ρ

/-- Robust feasibility of the original vector inequality (7.1.3). -/
def LSData.Robust {d k N : ℕ} (D : LSData d k N) (ρ : ℝ)
    (y : Fin d → ℝ) (τ : ℝ) : Prop :=
  ∀ η, D.Admissible ρ η →
    ‖(WithLp.toLp 2 (D.nominal y + ∑ i, (D.block i).effect y (η i)) :
      EuclideanSpace ℝ (Fin k))‖ ≤ τ

/-- System (7.1.11), including its lifted variables. The scalar expression uses
an all-ones p by q matrix, which is [1] on the specified 1 by 1 scalar blocks. -/
def LSData.LMI {d k N : ℕ} (D : LSData d k N) (ρ : ℝ)
    (y : Fin d → ℝ) (τ : ℝ)
    (Y : Fin N → Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ)
    (lam : Fin N → ℝ) : Prop :=
  (∀ i, (Y i).IsHermitian) ∧
  (∀ i ∈ D.scalar,
    let B := (D.block i).hatL.transpose * (Matrix.of (fun (_ : Fin (D.p i)) (_ : Fin (D.q i)) => (1 : ℝ))) * (D.block i).hatR y +
      ((D.block i).hatR y).transpose * (Matrix.of (fun (_ : Fin (D.q i)) (_ : Fin (D.p i)) => (1 : ℝ))) * (D.block i).hatL
    (Y i - B).PosSemidef ∧ (Y i + B).PosSemidef) ∧
  (∀ i, i ∉ D.scalar →
    (Matrix.fromBlocks
      (Y i - lam i • ((D.block i).hatL.transpose * (D.block i).hatL))
      ((D.block i).hatR y).transpose ((D.block i).hatR y)
      (lam i • (1 : Matrix (Fin (D.q i)) (Fin (D.q i)) ℝ))).PosSemidef) ∧
  (arrow (D.nominal y) τ - ρ • ∑ i, Y i).PosSemidef

/-- Projection of the explicit LMI system onto (y,τ). -/
def LSData.SDP {d k N : ℕ} (D : LSData d k N) (ρ : ℝ)
    (y : Fin d → ℝ) (τ : ℝ) : Prop :=
  ∃ Y lam, D.LMI ρ y τ Y lam

/-- Intermediate system (7.1.7)-(7.1.8), defined independently of the finite LMIs. -/
def LSData.Envelope {d k N : ℕ} (D : LSData d k N) (ρ : ℝ)
    (y : Fin d → ℝ) (τ : ℝ) : Prop :=
  ∃ Y : Fin N → Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ,
    (∀ i, (Y i).IsHermitian) ∧
    (∀ (i : Fin N) (η : Matrix (Fin (D.p i)) (Fin (D.q i)) ℝ), OperatorBound η 1 →
      (Y i - ((D.block i).hatL.transpose * η * (D.block i).hatR y +
        ((D.block i).hatR y).transpose * η.transpose * (D.block i).hatL)).PosSemidef) ∧
    (arrow (D.nominal y) τ - ρ • ∑ i, Y i).PosSemidef

end RobustOpt2009.CQApproximation

END IMPORTED LEAN SOURCE SNAPSHOT
-/

namespace RobustOpt2009.CQApproximation

/-- Theorem 7.1.2, printed pp. 182-183, PDF pp. 208-209: safety, radius
inflation by π/2, and exactness for a single block. -/
theorem least_squares_sdp {d k N : ℕ} (hk : 0 < k) (hN : 0 < N)
    (D : LSData d k N) (ρ : ℝ) (hρ : 0 < ρ) (y : Fin d → ℝ) (τ : ℝ) :
    (D.SDP ρ y τ → D.Robust ρ y τ) ∧
    (¬ D.SDP ρ y τ → ¬ D.Robust ((Real.pi / 2) * ρ) y τ) ∧
    (N = 1 → (D.SDP ρ y τ ↔ D.Robust ρ y τ)) := by sorry

end RobustOpt2009.CQApproximation
