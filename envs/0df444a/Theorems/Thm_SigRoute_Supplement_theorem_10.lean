-- Prove2me | Theorems.Thm_SigRoute_Supplement_theorem_10
-- name    : SigRoute.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:59:24.538575+00:00
-- url     : https://prove2.me/theorems/39357edd-d2e3-4e8a-9428-dc1c5e856767
-- title:
--   Theorem 10 — completeness: $\mathbb P[S<\tau]\le\exp\bigl(-2(N(1-\delta)u_{\min}-\tau)^2/(N u_{\max}^2)\bigr)$, and almost sure acceptance when $\delta_A=\delta_B=0$
-- statement:
--   Consider a routed verification protocol run for $N$ rounds by the honest prover on a true statement, with credits $u_A,u_B>0$ and threshold $\tau\in\mathbb R$. Write $u_{\min}=\min\{u_A,u_B\}$, $u_{\max}=\max\{u_A,u_B\}$ and $S=\sum_{j\le N}u_{\rho_j}a_j$ for the credit sum; the verifier accepts iff $S\ge\tau$. Assume the completeness hypothesis (HC) with errors $\delta_A,\delta_B$, and put $\delta=\max\{\delta_A,\delta_B\}$.
--
--   1. If $\tau\le N(1-\delta)u_{\min}$, the verifier rejects with probability at most
--   $$
--   \mathbb P[S<\tau]\ \le\ \exp\!\Bigl(-\frac{2\bigl(N(1-\delta)u_{\min}-\tau\bigr)^2}{N\,u_{\max}^2}\Bigr).
--   $$
--   2. If $\delta_A=\delta_B=0$ and $\tau\le N u_{\min}$, the verifier accepts almost surely: $S\ge\tau$ with probability one.
--
--   Together with the soundness bound of Theorem 14 this fixes the completeness error of the routed protocol: thresholds a little below $N(1-\delta)u_{\min}$ give exponentially small completeness error while the soundness bound stays exponentially small.
--
--   **Formalization Note** The honest run is any adapted routed run (`SigRoute.IsRoutedRun`) on any probability space satisfying (HC) in its conditional form (`SigRoute.Supplement.ArmComplete`). At $N=0$ the exponent's denominator is $0$ and Lean evaluates the bound to $1$; the event $\{S<\tau\}$ is then empty anyway.
--
--   Differences from the source:
--   - generalization: the honest prover's run on $x\in L$ → every probability space $(\Omega,\mu)$, filtration $(\mathcal F_j)$, post-base-stage σ-algebras $\mathcal G_j$ and adapted run $(\rho,a)$ (`IsRoutedRun`) satisfying (HC); reason: the honest prover's run is such a run, and the paper's proof uses only (HC) and adaptedness, so the theorem specializes to the paper's
--   - encoding: the hypotheses $x\in L$ and "the honest prover is used" → not modelled; reason: they enter only through (HC), which is a hypothesis of the statement
--   - encoding: rounds $j=1,\dots,N$ conditioned on $\mathcal F_{j-1}$, decisions $a_j\in\{0,1\}$ → 0-based rounds $j<N$ conditioned on `F j` / `G j`, decisions in `Bool`; reason: relabelling; same instances
--   - reading: (HC) "conditioned on $\mathcal F_{j-1}$ and on $\nu_j$ with $\rho_j=X$, the arm stage accepts with probability at least $1-\delta_X$" → $\mathbb P[a_j=1\mid\mathcal G_j]\ge1-\delta_{\rho_j}$ almost surely for $j<N$ (`ArmComplete`); reason: $\mathcal G_j$ is the σ-algebra of $(\mathcal F_{j-1},\nu_j)$ and $\rho_j$ is $\mathcal G_j$-measurable; the proof of Theorem 10 uses exactly this conditional form
--   - generalization: completeness errors $\delta_A,\delta_B$ (error probabilities) → arbitrary reals $\delta_A,\delta_B$; reason: the bound holds without a range restriction (for $\delta>1$ the conditional mean bound is implied by $Y_j\ge0$; $\delta_X<0$ makes (HC) unsatisfiable on rounds routed to $X$); it specializes to $\delta_X\in[0,1]$
--   - encoding: "the verifier rejects with probability" → `μ.real {ω | creditSum u ρ a N ω < τ}`; reason: rejection is the complement of acceptance $\{S\ge\tau\}$; the event is measurable, so this is the paper's probability
--   - reading: "the verifier always accepts" → $\tau\le S$ almost surely; reason: (HC) is a statement about conditional probabilities, which are defined up to null sets, so acceptance can only be asserted almost surely; a pointwise statement would be false on null sets the hypothesis cannot see
--   - encoding: the exponent at $N=0$ (division by $0$) → Lean's $x/0=0$, bound $1$; reason: at $N=0$ the paper's bound is undefined and the event $\{S<\tau\}$ is empty, so no instance changes
-- source:
--   Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Theorem 10, p.6

import Mathlib
import Definitions.Def_SigRoute_IsRoutedRun
import Definitions.Def_SigRoute_Supplement_ArmComplete

namespace SigRoute.Supplement

open MeasureTheory

/-- Theorem 10 (Completeness) (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission
manuscript (held version, sha256 d56b3b7a…), Theorem 10, p.6). Assume (HC), let `δ = max{δ_A, δ_B}` and
`x ∈ L`. If the honest prover is used and `τ ≤ N(1 − δ)u_min`, the verifier rejects with probability at
most `exp(−2(N(1 − δ)u_min − τ)² / (N u_max²))`. If `δ_A = δ_B = 0` and `τ ≤ N u_min`, the verifier
always accepts.

The two conjuncts: (i) the rejection bound `P[S < τ] ≤ exp(−2(N(1 − δ)u_min − τ)²/(N u_max²))`;
(ii) for `δ_A = δ_B = 0` and `τ ≤ N u_min`, acceptance `τ ≤ S` almost surely.

**Formalization Note** The honest prover's run on `x ∈ L` is any probability space `(Ω, μ)`, filtration
`F`, post-base-stage σ-algebras `G` and adapted run `(ρ, a)` (`IsRoutedRun`) satisfying (HC) in its
conditional form given `G j` (`ArmComplete`); rounds are 0-based. The verifier rejects on the strict event
`{S < τ}`, the complement of acceptance `{τ ≤ S}`. "Always accepts" is almost sure acceptance, since (HC)
is a statement about conditional probabilities. No range is imposed on `δ_A, δ_B`; at `N = 0` the
exponent's denominator is `0` and Lean's `x / 0 = 0` gives the trivial bound `1`. -/
theorem theorem_10 {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Filtration ℕ m) (G : ℕ → MeasurableSpace Ω)
    (ρ : ℕ → Ω → Arm) (a : ℕ → Ω → Bool) (hrun : IsRoutedRun F G ρ a)
    (u : Arm → ℝ) (hu : ∀ X, 0 < u X) (N : ℕ) (τ : ℝ) (δ : Arm → ℝ)
    (hHC : ArmComplete μ G ρ a N δ) :
    -- (i) the rejection bound
    (τ ≤ (N : ℝ) * (1 - max (δ Arm.A) (δ Arm.B)) * min (u Arm.A) (u Arm.B) →
      μ.real {ω | creditSum u ρ a N ω < τ}
        ≤ Real.exp (-2 * ((N : ℝ) * (1 - max (δ Arm.A) (δ Arm.B)) * min (u Arm.A) (u Arm.B) - τ) ^ 2
            / ((N : ℝ) * max (u Arm.A) (u Arm.B) ^ 2))) ∧
    -- (ii) perfect completeness: almost sure acceptance
    (δ Arm.A = 0 → δ Arm.B = 0 → τ ≤ (N : ℝ) * min (u Arm.A) (u Arm.B) →
      ∀ᵐ ω ∂μ, τ ≤ creditSum u ρ a N ω) := by sorry

end SigRoute.Supplement
