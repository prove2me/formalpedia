-- Prove2me | Theorems.Thm_RobustOpt2009_Adjustable_quadratic_rules_sdp
-- name    : RobustOpt2009.Adjustable.quadratic_rules_sdp
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:44:38.750433+00:00
-- url     : https://prove2.me/theorems/9daa7d3e-c668-454f-89a0-2d553943109f
-- title:
--   Corollary 14.3.8 — exact polynomial-size SDP for quadratic decision rules
-- statement:
--   Consider the affinely uncertain linear problem $\min\{c(z)^Tx+d(z):A(z)x\ge b(z)\}$ on $Z=\{z:\|Qz\|_2\le1\}$, where $Q$ has trivial kernel. For each variable fix an observation matrix $P_j\in\mathbb R^{k_j\times L}$ and allow every quadratic policy $X_j(z)=p_j+q_j^TP_jz+(P_jz)^TR_j(P_jz)$. Assume fixed recourse: whenever $P_j\ne0$, both the cost coefficient $c_j(z)$ and the constraint column $A_j(z)$ are independent of $z$.
--
--   For every threshold $t$ and every set of policy coefficients, the original robust constraints and the objective bound hold for all $z\in Z$ if and only if there exist $m+1$ nonnegative multipliers such that every explicit signed-slack certificate matrix $M_i$ from the model definition is positive semidefinite. The sets of attainable objective thresholds in the robust program and the SDP are equal. A fixed pair $(t,y)$ minimizes the robust program if and only if it extends by suitable multipliers to an SDP minimizer. Thus the restricted adjustable robust counterpart is represented exactly by the SDP minimizing $t$ subject to these conditions.
--
--   All certificate matrices depend affinely on the full SDP decision vector. There are $m+1$ PSD blocks, each of order $L+1$, $m+1$ nonnegativity constraints, and exactly
--   $$N=1+\sum_{j=1}^n(1+k_j+k_j^2)+(m+1)$$
--   scalar variables. With $K=\sum_jk_j$ and $B=1+n(1+K+K^2)+(m+1)$, one has $N\le B$ and at most $(B+1)(m+1)(L+1)^2$ scalar coefficients in the dense affine LMI matrices. These explicit counts express the polynomial-size SDP conclusion.
--
--   **Formalization Note** Exactness is within the prescribed quadratic policy class. The equivalence preserves every policy coefficient and objective threshold, so it handles infeasibility and unbounded optimization without using a real-valued infimum. It does not assert attainment of an optimum or unrestricted-policy optimality. Tractability is encoded by the explicit affine SDP and polynomial counts, rather than by an abstract tractability predicate or an additional bit-complexity claim.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Corollary 14.3.8, printed p. 385 (PDF p. 411), with (14.3.6) printed p. 375 (PDF p. 401) and fixed recourse in Definition 14.3.1, printed p. 371 (PDF p. 397).

import Definitions.Def_RobustOpt2009_Adjustable_Model

open scoped BigOperators

/- Imported definition source for blind auditing, copied verbatim from
Definitions.Def_RobustOpt2009_Adjustable_Model.

import Mathlib

open scoped BigOperators
noncomputable section

namespace RobustOpt2009.Adjustable

/-- The book's ellipsoid, using the Euclidean squared norm (not the Pi sup norm). -/
def ellipsoid {L r : ℕ} (Q : Matrix (Fin r) (Fin L) ℝ) : Set (Fin L → ℝ) :=
  {z | ∑ i, (Q.mulVec z i) ^ 2 ≤ 1}

/-- Index `none` is the distinguished top-left coordinate. -/
def momentBlock {L : ℕ} (s : ℝ) (v : Fin L → ℝ)
    (W : Matrix (Fin L) (Fin L) ℝ) : Matrix (Option (Fin L)) (Option (Fin L)) ℝ
  | none, none => s
  | none, some j => v j
  | some i, none => v i
  | some i, some j => W i j

def quadraticLift {L : ℕ} (z : Fin L → ℝ) :=
  momentBlock 0 z (fun i j => z i * z j)

def liftedHull {L r : ℕ} (Q : Matrix (Fin r) (Fin L) ℝ) :=
  convexHull ℝ (quadraticLift '' ellipsoid Q)

/-- The unshifted lift has 0 in its corner; only the PSD test has 1. -/
def momentRegion {L r : ℕ} (Q : Matrix (Fin r) (Fin L) ℝ) :
    Set (Matrix (Option (Fin L)) (Option (Fin L)) ℝ) :=
  {M | ∃ (v : Fin L → ℝ) (W : Matrix (Fin L) (Fin L) ℝ),
    M = momentBlock 0 v W ∧ (momentBlock 1 v W).PosSemidef ∧
      Matrix.trace (Q * W * Q.transpose) ≤ 1}

/-- Affinely uncertain LO data for (14.3.6), with a prescribed observation map per variable. -/
structure Model (L r n m : ℕ) (k : Fin n → ℕ) where
  Q : Matrix (Fin r) (Fin L) ℝ
  P : (j : Fin n) → Matrix (Fin (k j)) (Fin L) ℝ
  A0 : Matrix (Fin m) (Fin n) ℝ
  A1 : Fin L → Matrix (Fin m) (Fin n) ℝ
  b0 : Fin m → ℝ
  b1 : Fin L → Fin m → ℝ
  c0 : Fin n → ℝ
  c1 : Fin L → Fin n → ℝ
  d0 : ℝ
  d1 : Fin L → ℝ

/-- One constant, k_j linear coefficients and k_j² quadratic coefficients per policy. -/
abbrev CoeffIndex {n : ℕ} (k : Fin n → ℕ) :=
  (j : Fin n) × (Unit ⊕ (Fin (k j) ⊕ (Fin (k j) × Fin (k j))))

abbrev Row (m : ℕ) := Option (Fin m)

/-- Threshold, policy coefficients, and one multiplier for each row including the objective. -/
abbrev VarIndex {n : ℕ} (k : Fin n → ℕ) (m : ℕ) :=
  Unit ⊕ (CoeffIndex k ⊕ Row m)

variable {L r n m : ℕ} {k : Fin n → ℕ}

def constantCoeff (y : CoeffIndex k → ℝ) (j : Fin n) := y ⟨j, Sum.inl ()⟩
def linearCoeff (y : CoeffIndex k → ℝ) (j : Fin n) (a : Fin (k j)) :=
  y ⟨j, Sum.inr (Sum.inl a)⟩
def quadCoeff (y : CoeffIndex k → ℝ) (j : Fin n) (a b : Fin (k j)) :=
  y ⟨j, Sum.inr (Sum.inr (a, b))⟩

/-- Literal quadratic polynomial of P_j z, with all cross terms. -/
def policy (D : Model L r n m k) (y : CoeffIndex k → ℝ) (z : Fin L → ℝ)
    (j : Fin n) : ℝ :=
  constantCoeff y j + ∑ a, linearCoeff y j a * (D.P j).mulVec z a +
    ∑ a, ∑ b, quadCoeff y j a b * (D.P j).mulVec z a * (D.P j).mulVec z b

/-- Definition 14.3.1: certainty is required only on columns with nonzero observation maps. -/
def FixedRecourse (D : Model L r n m k) : Prop :=
  ∀ j, D.P j ≠ 0 → ∀ l, D.c1 l j = 0 ∧ ∀ i, D.A1 l i j = 0

/-- The exact robust epigraph in the prescribed quadratic policy class. -/
def robustEpigraph (D : Model L r n m k) (t : ℝ) (y : CoeffIndex k → ℝ) : Prop :=
  ∀ z ∈ ellipsoid D.Q,
    (∑ j, (D.c0 j + ∑ l, z l * D.c1 l j) * policy D y z j) +
      D.d0 + (∑ l, z l * D.d1 l) ≤ t ∧
    ∀ i, D.b0 i + (∑ l, z l * D.b1 l i) ≤
      ∑ j, (D.A0 i j + ∑ l, z l * D.A1 l i j) * policy D y z j

/-- Signed rows: `none` is t - c(z)'x - d(z); `some i` is A_i(z)x - b_i(z). -/
def rowCoeff0 (D : Model L r n m k) : Row m → Fin n → ℝ
  | none => fun j => -D.c0 j
  | some i => D.A0 i

def rowCoeff1 (D : Model L r n m k) : Row m → Fin L → Fin n → ℝ
  | none => fun l j => -D.c1 l j
  | some i => fun l j => D.A1 l i j

def rowOffset0 (D : Model L r n m k) (t : ℝ) : Row m → ℝ
  | none => t - D.d0
  | some i => -D.b0 i

def rowOffset1 (D : Model L r n m k) : Row m → Fin L → ℝ
  | none => fun l => -D.d1 l
  | some i => fun l => -D.b1 l i

def pulledLinear (D : Model L r n m k) (y : CoeffIndex k → ℝ) (j : Fin n)
    (l : Fin L) : ℝ := ∑ a, linearCoeff y j a * D.P j a l

/-- Symmetrization changes no quadratic polynomial; no restriction is placed on y. -/
def pulledQuadratic (D : Model L r n m k) (y : CoeffIndex k → ℝ) (j : Fin n)
    (l h : Fin L) : ℝ :=
  ∑ a, ∑ b, ((quadCoeff y j a b + quadCoeff y j b a) / 2) * D.P j a l * D.P j b h

def residualConstant (D : Model L r n m k) (t : ℝ) (y : CoeffIndex k → ℝ)
    (i : Row m) : ℝ := rowOffset0 D t i + ∑ j, rowCoeff0 D i j * constantCoeff y j

def residualLinear (D : Model L r n m k) (y : CoeffIndex k → ℝ)
    (i : Row m) (l : Fin L) : ℝ :=
  rowOffset1 D i l + ∑ j,
    (rowCoeff0 D i j * pulledLinear D y j l + rowCoeff1 D i l j * constantCoeff y j)

def residualQuadratic (D : Model L r n m k) (y : CoeffIndex k → ℝ)
    (i : Row m) (l h : Fin L) : ℝ :=
  ∑ j, rowCoeff0 D i j * pulledQuadratic D y j l h

def assemble (t : ℝ) (y : CoeffIndex k → ℝ) (lam : Row m → ℝ) : VarIndex k m → ℝ
  | Sum.inl _ => t
  | Sum.inr (Sum.inl a) => y a
  | Sum.inr (Sum.inr i) => lam i

def threshold (u : VarIndex k m → ℝ) : ℝ := u (Sum.inl ())
def coefficients (u : VarIndex k m → ℝ) (a : CoeffIndex k) : ℝ := u (Sum.inr (Sum.inl a))
def multiplier (u : VarIndex k m → ℝ) (i : Row m) : ℝ := u (Sum.inr (Sum.inr i))

/-- Explicit LMI of order L+1; its affine dependence on all decision variables is a theorem. -/
def certificateMatrix (D : Model L r n m k) (u : VarIndex k m → ℝ) (i : Row m) :=
  momentBlock (residualConstant D (threshold u) (coefficients u) i - multiplier u i)
    (fun l => residualLinear D (coefficients u) i l / 2)
    (fun l h => residualQuadratic D (coefficients u) i l h +
      multiplier u i * (D.Q.transpose * D.Q) l h)

/-- The SDP minimizes `threshold u` over this explicitly defined feasible set. -/
def sdpFeasible (D : Model L r n m k) (u : VarIndex k m → ℝ) : Prop :=
  (∀ i, 0 ≤ multiplier u i) ∧ ∀ i, (certificateMatrix D u i).PosSemidef

/-- An attained minimum of the original restricted robust program; existence is not assumed. -/
def robustOptimal (D : Model L r n m k) (t : ℝ) (y : CoeffIndex k → ℝ) : Prop :=
  robustEpigraph D t y ∧ ∀ (s : ℝ) (y' : CoeffIndex k → ℝ),
    robustEpigraph D s y' → t ≤ s

/-- An attained minimum of the explicit SDP with its linear threshold objective. -/
def sdpOptimal (D : Model L r n m k) (u : VarIndex k m → ℝ) : Prop :=
  sdpFeasible D u ∧ ∀ v : VarIndex k m → ℝ, sdpFeasible D v → threshold u ≤ threshold v

def observationSize (k : Fin n → ℕ) : ℕ := ∑ j, k j

def variableBound (k : Fin n → ℕ) (m : ℕ) : ℕ :=
  1 + n * (1 + observationSize k + observationSize k ^ 2) + (m + 1)

/-- Dense affine LMI storage: constant matrix plus one coefficient matrix per variable. -/
def denseLMICoefficientCount (L : ℕ) (k : Fin n → ℕ) (m : ℕ) : ℕ :=
  (Fintype.card (VarIndex k m) + 1) * Fintype.card (Row m) *
    Fintype.card (Option (Fin L)) ^ 2

end RobustOpt2009.Adjustable

-/

namespace RobustOpt2009.Adjustable

/-- Corollary 14.3.8, printed p. 385 (PDF 411): exact SDP with explicit polynomial sizes. -/
theorem quadratic_rules_sdp {L r n m : ℕ} (k : Fin n → ℕ) (D : Model L r n m k)
    (hQ : Function.Injective D.Q.mulVec) (hrec : FixedRecourse D) :
    (∀ (t : ℝ) (y : CoeffIndex k → ℝ), robustEpigraph D t y ↔
      ∃ lam : Row m → ℝ, sdpFeasible D (assemble t y lam)) ∧
    {t : ℝ | ∃ y : CoeffIndex k → ℝ, robustEpigraph D t y} =
      threshold '' {u : VarIndex k m → ℝ | sdpFeasible D u} ∧
    (∀ (t : ℝ) (y : CoeffIndex k → ℝ), robustOptimal D t y ↔
      ∃ lam : Row m → ℝ, sdpOptimal D (assemble t y lam)) ∧
    (∀ (u v : VarIndex k m → ℝ) (a b : ℝ), a + b = 1 → ∀ i,
      certificateMatrix D (a • u + b • v) i =
        a • certificateMatrix D u i + b • certificateMatrix D v i) ∧
    Fintype.card (VarIndex k m) = 1 + (∑ j, (1 + k j + (k j) ^ 2)) + (m + 1) ∧
    Fintype.card (Row m) = m + 1 ∧
    Fintype.card (Option (Fin L)) = L + 1 ∧
    Fintype.card (VarIndex k m) ≤ variableBound k m ∧
    denseLMICoefficientCount L k m ≤
      (variableBound k m + 1) * (m + 1) * (L + 1) ^ 2 := by sorry

end RobustOpt2009.Adjustable
