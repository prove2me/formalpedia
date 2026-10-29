-- Prove2me | Theorems.Thm_WangMinimaxRegret_Reformulation_theorem_1
-- name    : WangMinimaxRegret.Reformulation.theorem_1
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:35:26.672571+00:00
-- url     : https://prove2.me/theorems/23486e09-ef95-4c17-b4d6-429e87157294
-- title:
--   Theorem 1 — full robust screening LP equivalence
-- statement:
--   Let $a\ge0$, $b\in\mathbb R\cup\{+\infty\}$, $a\le b$, and let $K\ge0$ finite moments be consistent with a Borel probability law on $I=[a,b]$ whose right-continuous CDF satisfies $F(a)=0$. The ambiguity class $\mathcal F$ consists of all such laws with the specified finite moments. Let $\mathcal M$ be the normalized, nonnegative, nondecreasing, right-continuous Stieltjes payments satisfying $\int_{I\cap(0,x]}t^{-1}\,dm(t)\le1$ for every $x\in I$. Define the original competitive ratio from actual seller and posted-price revenues, and let $V_P=\sup_{m\in\mathcal M}C(m)$.
--
--   Independently define (P-LP) to maximize real $r\ge0$ over $m\in\mathcal M$ and arbitrary real price-indexed functions $\lambda_k(p)$ subject to
--   $$\sum_{k=1}^K(x^k-\mu_k)\lambda_k(p)\le m(x)\quad(p,x\in I,\ x<p),$$
--   $$rp+\sum_{k=1}^K(x^k-\mu_k)\lambda_k(p)\le m(x)\quad(p,x\in I,\ p\le x).$$
--   Let its supremal value be $V_{LP}$. The theorem asserts all of the following:
--
--   1. $V_P=V_{LP}$.
--   2. For every fixed $m\in\mathcal M$ and real $r\ge0$, $r\le C(m)$ if and only if there is a multiplier family $\lambda$ making $(m,r,\lambda)$ LP feasible.
--   3. Every optimal LP triple has $r=V_P=C(m)$ and $m$ is an optimal original payment.
--   4. Every optimal original payment lifts to an optimal LP triple with the same payment and $r=C(m)$.
--   5. The original supremum is attained if and only if the LP supremum is attained.
--
--   These are conditional optimizer assertions, not an unconditional existence claim. For finite positive benchmarks $C(m)$ is the printed worst-case revenue quotient; otherwise the operational extension is the supremum of nonnegative rates satisfying $rpF([p,\infty))\le\int m\,dF$ for every feasible law and finite price. No certificate is used to define $C(m)$. The fixed-payment reading in clause 2 retains the source's substitution argument and its known counterexample; the counterexample alone does not disprove equality of the globally optimized values.
--
--   Differences from the source:
--   - encoding: real interval, payment functions, probability laws, and moment orders 1 through K → real-line Borel measures supported on the interval, Stieltjes functions extended by zero below a and constantly above finite b, and Fin K exponents i+1; reason: extensions only fix values outside the domain; all atoms and payment jumps are retained, including the payment atom at a>0
--   - encoding: the seller knows moments of an actual valuation distribution → Consistent d requires a nonempty printed ambiguity class, with finite specified moments; reason: makes the standing information-consistency assumption explicit; no interiority, positive variance, or density is assumed
--   - reading: the notation [a,b] also occurs with b=infinity later in the paper → b has type WithTop real; prices and valuations remain finite; hindsight revenue is a supremum, and the competitive ratio uses all price-wise revenue inequalities; reason: specifies the support-only unbounded cases where the printed ratio may be infinity/infinity; finite positive benchmarks retain the usual quotient
--   - encoding: nonnegative revenue integrals and optimization infima/suprema → nonnegative extended integrals and ENNReal/EReal extrema; zero-tail laws impose no fractional constraint; reason: avoids nonintegrable real integrals defaulting to zero and empty real extrema; empty infima are positive infinity
--   - reading: (P) is equivalent to (P-LP), with optimal ratio and payment identification → value equality, exact fixed-payment feasible projection, both optimizer transfers, and equivalence of attainment; reason: the substitution preceding Theorem 1 supports this full reading of equivalent; the fixed-payment counterexample is retained separately
--   - encoding: K-tuples of real functions on the price interval → functions on the real line constrained only for prices in I; reason: unrestricted extension outside I changes no feasible price-indexed family
-- source:
--   Wang, Liu and Zhang (2024), Minimax Regret Robust Screening with Moment Information, https://doi.org/10.1287/msom.2023.0072, Section 2, p. 9, Theorem 1 and (P-LP)

import Definitions.Def_WangMinimaxRegret_Reformulation_Programs

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

/-
Imported dependency source, reproduced verbatim for the standalone blind audit.

import Mathlib

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false
noncomputable section

namespace WangMinimaxRegret.Reformulation

/-- A nonnegative measure linear program, with finite real constraint integrals
and a possibly infinite nonnegative objective. No probability normalization is implicit. -/
structure MeasureLP (ι : Type) where
  carrier : Set ℝ
  cost : ℝ → ℝ≥0∞
  test : ι → ℝ → ℝ
  target : ι → ℝ

def MeasureLP.Feasible {ι : Type} (L : MeasureLP ι) (H : Measure ℝ) : Prop :=
  IsFiniteMeasure H ∧ H L.carrierᶜ = 0 ∧
    ∀ i, Integrable (L.test i) H ∧ (∫ x, L.test i x ∂H) = L.target i

def MeasureLP.objective {ι : Type} (L : MeasureLP ι) (H : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, L.cost x ∂H

def MeasureLP.value {ι : Type} (L : MeasureLP ι) : ℝ≥0∞ :=
  ⨅ H : Measure ℝ, ⨅ (_ : L.Feasible H), L.objective H

end WangMinimaxRegret.Reformulation

import Mathlib

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false
noncomputable section

namespace WangMinimaxRegret.Reformulation

structure Data where
  a : ℝ
  b : WithTop ℝ
  nonneg_a : 0 ≤ a
  ordered : (a : WithTop ℝ) ≤ b
  K : ℕ
  mu : Fin K → ℝ

def interval (d : Data) : Set ℝ := {x | d.a ≤ x ∧ (x : WithTop ℝ) ≤ d.b}

/-- The law's right-continuous CDF; laws below are Borel measures on the real line. -/
def cdf (F : Measure ℝ) (x : ℝ) : ℝ≥0∞ := F (Iic x)

/-- Display (2), which does not impose F(a)=0. Order zero is total mass one. -/
def MomentLaw (d : Data) (F : Measure ℝ) : Prop :=
  IsProbabilityMeasure F ∧ F (interval d)ᶜ = 0 ∧
    ∀ i : Fin d.K, Integrable (fun x : ℝ => x ^ (i.val + 1)) F ∧
      (∫ x : ℝ, x ^ (i.val + 1) ∂F) = d.mu i

/-- The printed ambiguity class, including its lower-endpoint restriction. -/
def Ambiguous (d : Data) (F : Measure ℝ) : Prop :=
  MomentLaw d F ∧ cdf F d.a = 0

def Consistent (d : Data) : Prop := ∃ F : Measure ℝ, Ambiguous d F

/-- Cumulative allocation from the payment Stieltjes measure. Integrate only at
positive valuations; the zero atom is forbidden by the payment normalization. -/
def allocation (d : Data) (m : StieltjesFunction ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in interval d ∩ Ioc 0 x, ENNReal.ofReal (1 / t) ∂m.measure

/-- The payment's zero/constant extensions only specify values outside the valuation domain.
StieltjesFunction supplies monotonicity and right continuity, without finite total variation. -/
def IsPayment (d : Data) (m : StieltjesFunction ℝ) : Prop :=
  m 0 = 0 ∧ (∀ x : ℝ, x < d.a → m x = 0) ∧
  (∀ x y : ℝ, d.b ≤ (x : WithTop ℝ) → d.b ≤ (y : WithTop ℝ) → m x = m y) ∧
  (∀ x ∈ interval d, 0 ≤ m x) ∧
  ∀ x ∈ interval d, allocation d m x ≤ 1

/-- The economic direct-mechanism inequalities, independently of the payment budget. -/
def DirectICIR (d : Data) (q m : ℝ → ℝ) : Prop :=
  (∀ x ∈ interval d, 0 ≤ q x ∧ q x ≤ 1) ∧
  (∀ x ∈ interval d, 0 ≤ x * q x - m x) ∧
  ∀ x ∈ interval d, ∀ y ∈ interval d, x * q y - m y ≤ x * q x - m x

end WangMinimaxRegret.Reformulation

import Definitions.Def_WangMinimaxRegret_Reformulation_Model

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false
noncomputable section

namespace WangMinimaxRegret.Reformulation

def tail (F : Measure ℝ) (p : ℝ) : ℝ≥0∞ := F (Ici p)

def revenue (m : StieltjesFunction ℝ) (F : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (m x) ∂F

def priceRevenue (F : Measure ℝ) (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal p * tail F p

def benchmark (d : Data) (F : Measure ℝ) : ℝ≥0∞ :=
  ⨆ p ∈ interval d, priceRevenue F p

/-- Operational ratio, defined entirely from actual revenues, even for infinite benchmarks. -/
def competitiveRatio (d : Data) (m : StieltjesFunction ℝ) : ℝ≥0∞ :=
  ⨆ r : ℝ≥0, ⨆ (_ : ∀ F : Measure ℝ, Ambiguous d F →
    ∀ p ∈ interval d, (r : ℝ≥0∞) * priceRevenue F p ≤ revenue m F), (r : ℝ≥0∞)

/-- Used only under finite, strictly positive benchmark hypotheses. -/
def quotientRatio (d : Data) (m : StieltjesFunction ℝ) : ℝ≥0∞ :=
  ⨅ F : Measure ℝ, ⨅ (_ : Ambiguous d F), revenue m F / benchmark d F

def originalValue (d : Data) : EReal :=
  ⨆ m : StieltjesFunction ℝ, ⨆ (_ : IsPayment d m), (competitiveRatio d m : EReal)

def OriginalOptimal (d : Data) (m : StieltjesFunction ℝ) : Prop :=
  IsPayment d m ∧ (competitiveRatio d m : EReal) = originalValue d

/-- Zero-tail laws impose no constraint: the empty infimum is positive infinity. -/
def fractionalValue (laws : Set (Measure ℝ)) (m : StieltjesFunction ℝ) (p : ℝ) : ℝ≥0∞ :=
  ⨅ F ∈ laws, ⨅ (_ : 0 < tail F p), revenue m F / tail F p

def HypographFeasible (d : Data) (m : StieltjesFunction ℝ) (r : ℝ) : Prop :=
  IsPayment d m ∧ ∀ p ∈ interval d,
    ((r * p : ℝ) : EReal) ≤ (fractionalValue {F | Ambiguous d F} m p : EReal)

def hypographValue (d : Data) : EReal :=
  ⨆ m : StieltjesFunction ℝ, ⨆ r : ℝ, ⨆ (_ : HypographFeasible d m r), (r : EReal)

end WangMinimaxRegret.Reformulation

import Definitions.Def_WangMinimaxRegret_Reformulation_MeasureLP
import Definitions.Def_WangMinimaxRegret_Reformulation_Revenue

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false
noncomputable section

namespace WangMinimaxRegret.Reformulation

/-- Equation (3) as a measure LP. The none row is tail mass one; the some rows
are centered moments. The redundant k=0 equation is identically zero. -/
def homogenizedLP (d : Data) (m : StieltjesFunction ℝ) (p : ℝ) : MeasureLP (Option (Fin d.K)) where
  carrier := interval d
  cost := fun x => ENNReal.ofReal (m x)
  test := fun i => match i with
    | none => (Ici p).indicator (fun _ => (1 : ℝ))
    | some j => fun x => x ^ (j.val + 1) - d.mu j
  target := fun i => match i with
    | none => 1
    | some _ => 0

def scaleToTail (F : Measure ℝ) (p : ℝ) : Measure ℝ := (tail F p)⁻¹ • F

def normalizeMass (H : Measure ℝ) : Measure ℝ := (H univ)⁻¹ • H

def momentPolynomial (d : Data) (lam : Fin d.K → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin d.K, (x ^ (i.val + 1) - d.mu i) * lam i

/-- The two distinct half-interval inequalities of (4). -/
def DualFeasible (d : Data) (m : StieltjesFunction ℝ) (p theta : ℝ)
    (lam : Fin d.K → ℝ) : Prop :=
  (∀ x ∈ interval d, x < p → momentPolynomial d lam x ≤ m x) ∧
  ∀ x ∈ interval d, p ≤ x → theta + momentPolynomial d lam x ≤ m x

def dualValue (d : Data) (m : StieltjesFunction ℝ) (p : ℝ) : EReal :=
  ⨆ theta : ℝ, ⨆ lam : Fin d.K → ℝ, ⨆ (_ : DualFeasible d m p theta lam),
    (theta : EReal)

/-- Price-indexed multipliers have no regularity restriction. -/
def LPFeasible (d : Data) (m : StieltjesFunction ℝ) (r : ℝ)
    (lam : ℝ → Fin d.K → ℝ) : Prop :=
  IsPayment d m ∧ 0 ≤ r ∧ ∀ p ∈ interval d, DualFeasible d m p (r * p) (lam p)

def lpValue (d : Data) : EReal :=
  ⨆ m : StieltjesFunction ℝ, ⨆ r : ℝ, ⨆ lam : ℝ → Fin d.K → ℝ,
    ⨆ (_ : LPFeasible d m r lam), (r : EReal)

def LPOptimal (d : Data) (m : StieltjesFunction ℝ) (r : ℝ)
    (lam : ℝ → Fin d.K → ℝ) : Prop :=
  LPFeasible d m r lam ∧ (r : EReal) = lpValue d

end WangMinimaxRegret.Reformulation

-/

namespace WangMinimaxRegret.Reformulation

theorem theorem_1 (d : Data) (hc : Consistent d) :
    originalValue d = lpValue d ∧
    (∀ (m : StieltjesFunction ℝ) (r : ℝ), IsPayment d m → 0 ≤ r →
      ((r : EReal) ≤ (competitiveRatio d m : EReal) ↔
        ∃ lam : ℝ → Fin d.K → ℝ, LPFeasible d m r lam)) ∧
    (∀ (m : StieltjesFunction ℝ) (r : ℝ) (lam : ℝ → Fin d.K → ℝ),
      LPOptimal d m r lam →
        (r : EReal) = originalValue d ∧
        (r : EReal) = (competitiveRatio d m : EReal) ∧ OriginalOptimal d m) ∧
    (∀ m : StieltjesFunction ℝ, OriginalOptimal d m →
      ∃ (r : ℝ) (lam : ℝ → Fin d.K → ℝ),
        (r : EReal) = (competitiveRatio d m : EReal) ∧ LPOptimal d m r lam) ∧
    ((∃ m : StieltjesFunction ℝ, OriginalOptimal d m) ↔
      ∃ (m : StieltjesFunction ℝ) (r : ℝ) (lam : ℝ → Fin d.K → ℝ), LPOptimal d m r lam) := by sorry

end WangMinimaxRegret.Reformulation
