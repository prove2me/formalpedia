-- Prove2me | Theorems.Thm_RobustOpt2009_ScalarChance_theorem_2_4_4
-- name    : RobustOpt2009.ScalarChance.theorem_2_4_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:42:29.524517+00:00
-- url     : https://prove2.me/theorems/1d7ffb5d-1634-44b0-a931-3b733088ca70
-- title:
--   Theorem 2.4.4 — Safe robust counterpart with known support bounds
-- statement:
--   Let $\zeta_1,\ldots,\zeta_L$ be independent measurable real random variables on a probability space $(S,\mathcal F,P)$. Fix real parameters $\mu_i^-\le\mu_i^+$ and $\sigma_i\ge0$ such that, for every real $t$,
--   $$\mathbb E_P e^{t\zeta_i}\le \exp\!\left(\max\{\mu_i^-t,\mu_i^+t\}+\tfrac12\sigma_i^2t^2\right).$$
--   These exponential expectations are finite. Write $B(y)=\sum_i\max\{\mu_i^-y_i,\mu_i^+y_i\}$ and $D(y)=\sqrt{\sum_i\sigma_i^2y_i^2}$.
--
--   For deterministic linear-constraint data $a^0,a^i\in\mathbb R^n$ and $b^0,b^i\in\mathbb R$, put $z_0(x)=(a^0)^Tx-b^0$ and $z_i(x)=(a^i)^Tx-b^i$. Robust feasibility over a set $Z$ means $z_0(x)+\sum_i\eta_i z_i(x)\le0$ for every $\eta\in Z$.
--
--   Suppose also that $a_i^-\le\mu_i^-\le\mu_i^+\le a_i^+$ are finite real endpoints and $a_i^-\le\zeta_i\le a_i^+$ almost surely. Let $0<\varepsilon<1$ and $r_\varepsilon=\sqrt{2\log(1/\varepsilon)}$. Let $Z$ contain exactly those $\eta$ satisfying $a_i^-\le\eta_i\le a_i^+$ and admitting $w$ with $\mu_i^-\le\eta_i-\sigma_iw_i\le\mu_i^+$ for every $i$ and $\sqrt{\sum_iw_i^2}\le r_\varepsilon$.
--
--   Robust feasibility of $x$ over $Z$ is equivalent to the existence of extended vectors $u=(u_0,u_1,\ldots,u_L)$ and $v=(v_0,v_1,\ldots,v_L)$ such that
--   $$z_i(x)=u_i+v_i\quad(0\le i\le L),$$
--   $$u_0+\sum_i\max\{a_i^-u_i,a_i^+u_i\}\le0,\qquad v_0+B(v)+r_\varepsilon D(v)\le0.$$
--   This is a convex system in $(x,u,v)$. Every feasible triple also satisfies
--   $$P\{z_0(x)+\sum_i\zeta_i z_i(x)>0\}\le\varepsilon.$$
--   Thus the exact robust representation yields a safe approximation to the scalar chance constraint with the additional support information.
--
--   **Formalization Note** The nominal coordinate is a separate real component, and `Fin L` indexes the book's coordinates $1,\ldots,L$. Probabilities use the real evaluation of a probability measure. Measurability is explicit, and finite exponential expectations are expressed with integrability. The strict violation event is preserved; zero $\sigma_i$ and zero-dimensional sums are allowed. The scaled-coordinate set represents the source’s zero-denominator convention, and the nominal coordinate is split as well as the random coordinates.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Theorem 2.4.4, (2.4.12)–(2.4.14), printed p. 48 (PDF p. 74).

import Definitions.Def_RobustOpt2009_ScalarChance_Setting

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/- Imported dependency source for blind auditing (verbatim):
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RobustOpt2009.ScalarChance

/-- Residual coordinates of (2.2.1); the nominal coordinate is stored separately. -/
noncomputable def residual {L n : ℕ} (a0 : Fin n → ℝ) (b0 : ℝ)
    (a : Fin L → Fin n → ℝ) (b : Fin L → ℝ) (x : Fin n → ℝ) :
    ℝ × (Fin L → ℝ) :=
  ((∑ j, a0 j * x j) - b0, fun i => (∑ j, a i j * x j) - b i)

/-- Robust feasibility of the affine residual for every perturbation in Z. -/
def RobustFeasible {L : ℕ} (Z : Set (Fin L → ℝ)) (z : ℝ × (Fin L → ℝ)) : Prop :=
  ∀ η ∈ Z, z.1 + ∑ i, η i * z.2 i ≤ 0

/-- Strict violation probability, (2.2.2) and (2.4.5). -/
noncomputable def violation {L : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Measure S) (ζ : Fin L → S → ℝ) (z : ℝ × (Fin L → ℝ)) : ℝ :=
  P.real {ω | 0 < z.1 + ∑ i, ζ i ω * z.2 i}

/-- P.2, including finite exponential expectations so the Bochner integral is genuine.
Parameter order and nonnegative sigma are separate theorem hypotheses. -/
def MGFMajorant {L : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Measure S) (ζ : Fin L → S → ℝ) (μminus μplus σ : Fin L → ℝ) : Prop :=
  ∀ (i : Fin L) (t : ℝ),
    Integrable (fun ω => Real.exp (t * ζ i ω)) P ∧
    (∫ ω, Real.exp (t * ζ i ω) ∂P) ≤
      Real.exp (max (μminus i * t) (μplus i * t) + (σ i)^2 * t^2 / 2)

/-- The deterministic box contribution in (2.4.8), for any lower and upper endpoints. -/
noncomputable def boxTerm {L : ℕ} (lo hi y : Fin L → ℝ) : ℝ :=
  ∑ i, max (lo i * y i) (hi i * y i)

/-- The weighted Euclidean term in (2.4.8). Zero sigma is permitted. -/
noncomputable def deviation {L : ℕ} (σ y : Fin L → ℝ) : ℝ :=
  Real.sqrt (∑ i, (σ i)^2 * (y i)^2)

/-- The radius in (2.4.10) and (2.4.13); used with 0 < ε < 1. -/
noncomputable def radius (ε : ℝ) : ℝ := Real.sqrt (2 * Real.log (1 / ε))

/-- The left side of the explicit convex constraint (2.4.8). -/
noncomputable def safeValue {L : ℕ} (μminus μplus σ : Fin L → ℝ) (ε : ℝ)
    (z : ℝ × (Fin L → ℝ)) : ℝ :=
  z.1 + boxTerm μminus μplus z.2 + radius ε * deviation σ z.2

/-- The moment uncertainty set (2.4.10). Writing the displacement as σ_i w_i
implements the printed extended-real convention for division by zero. -/
def momentSet {L : ℕ} (μminus μplus σ : Fin L → ℝ) (ε : ℝ) : Set (Fin L → ℝ) :=
  {η | ∃ w : Fin L → ℝ,
    (∀ i, μminus i ≤ η i - σ i * w i ∧ η i - σ i * w i ≤ μplus i) ∧
    Real.sqrt (∑ i, (w i)^2) ≤ radius ε}

/-- The intersection with the known support box, (2.4.13). -/
def boundedMomentSet {L : ℕ} (alo ahi μminus μplus σ : Fin L → ℝ) (ε : ℝ) :
    Set (Fin L → ℝ) :=
  {η | η ∈ momentSet μminus μplus σ ε ∧ ∀ i, alo i ≤ η i ∧ η i ≤ ahi i}

/-- The three constraints (2.4.14), including the nominal-coordinate split. -/
def SplitSystem {L : ℕ} (alo ahi μminus μplus σ : Fin L → ℝ) (ε : ℝ)
    (z u v : ℝ × (Fin L → ℝ)) : Prop :=
  z.1 = u.1 + v.1 ∧ (∀ i, z.2 i = u.2 i + v.2 i) ∧
  u.1 + boxTerm alo ahi u.2 ≤ 0 ∧ safeValue μminus μplus σ ε v ≤ 0

/-- Box intersected with a Euclidean ball, (2.3.9). -/
def boxBall {L : ℕ} (r : ℝ) : Set (Fin L → ℝ) :=
  {η | (∀ i, |η i| ≤ 1) ∧ Real.sqrt (∑ i, (η i)^2) ≤ r}

/-- The lifted conic system (2.3.10), with its printed negative residual sign. -/
def BoxBallSystem {L : ℕ} (r : ℝ) (z : ℝ × (Fin L → ℝ))
    (p q : Fin L → ℝ) : Prop :=
  (∀ i, p i + q i = -z.2 i) ∧
  (∑ i, |p i|) + r * Real.sqrt (∑ i, (q i)^2) ≤ -z.1

/-- The log-MGF upper bound Φ, (2.4.2). -/
noncomputable def phi {L : ℕ} (μminus μplus σ w : Fin L → ℝ) : ℝ :=
  ∑ i, (max (μminus i * w i) (μplus i * w i) + (σ i)^2 * (w i)^2 / 2)

/-- The exponential-certificate set Zε^o preceding (2.4.6), not a perturbation set. -/
def exponentialCertificateSet {L : ℕ} (μminus μplus σ : Fin L → ℝ) (ε : ℝ) :
    Set (ℝ × (Fin L → ℝ)) :=
  {z | ∃ α : ℝ, 0 < α ∧ α * z.1 + phi μminus μplus σ (fun i => α * z.2 i) ≤ Real.log ε}

/-- The closure Zε in (2.4.6), distinct from the uncertainty set in (2.4.10). -/
def closedCertificateSet {L : ℕ} (μminus μplus σ : Fin L → ℝ) (ε : ℝ) :
    Set (ℝ × (Fin L → ℝ)) :=
  closure (exponentialCertificateSet μminus μplus σ ε)

end RobustOpt2009.ScalarChance
-/

namespace RobustOpt2009.ScalarChance

theorem theorem_2_4_4 {L n : ℕ} {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (ζ : Fin L → S → ℝ) (hmeas : ∀ i, Measurable (ζ i))
    (hindep : iIndepFun ζ P)
    (μminus μplus σ : Fin L → ℝ)
    (hμ : ∀ i, μminus i ≤ μplus i) (hσ : ∀ i, 0 ≤ σ i)
    (hmgf : MGFMajorant P ζ μminus μplus σ) (alo ahi : Fin L → ℝ)
    (hlo : ∀ i, alo i ≤ μminus i) (hhi : ∀ i, μplus i ≤ ahi i)
    (hsupport : ∀ i, ∀ᵐ ω ∂P, alo i ≤ ζ i ω ∧ ζ i ω ≤ ahi i)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1) (a0 : Fin n → ℝ) (b0 : ℝ) (a : Fin L → Fin n → ℝ) (b : Fin L → ℝ) :
    (∀ x, RobustFeasible (boundedMomentSet alo ahi μminus μplus σ ε)
        (residual a0 b0 a b x) ↔
      ∃ u v, SplitSystem alo ahi μminus μplus σ ε (residual a0 b0 a b x) u v) ∧
    (∀ x u v, SplitSystem alo ahi μminus μplus σ ε (residual a0 b0 a b x) u v →
      violation P ζ (residual a0 b0 a b x) ≤ ε) ∧
    Convex ℝ {t : (Fin n → ℝ) × (ℝ × (Fin L → ℝ)) × (ℝ × (Fin L → ℝ)) |
      SplitSystem alo ahi μminus μplus σ ε (residual a0 b0 a b t.1) t.2.1 t.2.2} := by sorry

end RobustOpt2009.ScalarChance
