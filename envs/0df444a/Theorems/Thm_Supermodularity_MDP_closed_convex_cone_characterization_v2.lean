-- Prove2me | Theorems.Thm_Supermodularity_MDP_closed_convex_cone_characterization_v2
-- name    : Supermodularity.MDP.closed_convex_cone_characterization_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:34.626512+00:00
-- url     : https://prove2.me/theorems/ece3f47e-9b9f-4c57-8666-782f4987a56b
-- title:
--   Theorem 3.9.1 - closed convex cone characterization of the integral (corrected: $V$ contains the constants; probability measures; Borel sets and functions)
-- statement:
--   Let $T \subseteq \mathbb{R}^m$, let $\{F(t,\cdot) : t \in T\}$ be a family of distribution functions on $\mathbb{R}^n$, represented by probability measures $\mu_t$ on the Borel sets of $\mathbb{R}^n$, and let $V$ be a set of real-valued functions on $T$ that is a **closed convex cone containing the constant functions**: $V$ is closed in the topology of pointwise convergence on $T \to \mathbb{R}$, closed under addition and under multiplication by nonnegative scalars, and contains every constant function $t \mapsto c$ ($c \in \mathbb{R}$).
--
--   Then the following are equivalent:
--
--   1. $t \mapsto \int_S dF(t,w) = \mu_t(S)$ belongs to $V$ for every Borel increasing (upward-closed) set $S \subseteq \mathbb{R}^n$;
--   2. $t \mapsto \int h(w)\, dF(t,w)$ belongs to $V$ for every Borel measurable increasing function $h : \mathbb{R}^n \to \mathbb{R}$ that is $\mu_t$-integrable for every $t \in T$.
--
--   This is Topkis's Theorem 3.9.1 with the correction below. It generalizes Lehmann's characterization of stochastic monotonicity (the case $V$ = increasing functions of $t$) to any property of $t \mapsto \int h\,dF(t,w)$ defined by such a cone, in particular supermodularity and convexity or concavity in $t$ (Corollary 3.9.1), which is how stochastic supermodularity of the transition law enters Theorem 3.9.2.
--
--   **Formalization Note.** The retired version assumed only that $V$ is a closed convex cone and was disproved with $V$ = the nonnegative functions on $T$: every $\mu_t(S)$ is nonnegative, so (1) holds, but the increasing function $h \equiv -1$ has integral $-1 \notin V$. The proof of (1) $\Rightarrow$ (2) writes a bounded increasing $h$ as a constant plus a limit of nonnegative combinations of indicators of increasing sets (layer-cake), so it needs the (possibly negative) constants to lie in $V$; every cone the book applies the theorem to (increasing, supermodular, convex functions of $t$) contains them. The new statement adds this hypothesis; if the printed statement already carries it, the retired version dropped a hypothesis rather than the source being in error, and the corrected statement is the same either way. Two conventions are made explicit as well: the $\mu_t$ are probability measures (the book's distribution functions; the retired version allowed arbitrary measures, for which the constant term $c\,\mu_t(\mathbb{R}^n)$ is not a constant function), and the increasing sets $S$ and increasing functions $h$ are Borel measurable, which is what $\int_S dF$ and $\int h\,dF$ presuppose (for $n \ge 2$ an upward-closed set or an increasing function need not be Borel; the retired version evaluated the outer measure on arbitrary upward-closed sets). Integrability of $h$ against every $\mu_t$ is retained as the explicit form of "for which the integral exists"; with it, (1) $\Rightarrow$ (2) follows from the bounded case by truncation and dominated convergence, using the pointwise closedness of $V$.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 1998 (reprint 2011), p. 159-160, Theorem 3.9.1 — corrected statement: the closed convex cone V is required to contain the constant functions (as every cone the book applies it to does, and as the proof needs)

import Mathlib

open MeasureTheory

namespace Supermodularity.MDP

/-- Theorem 3.9.1 (Topkis, *Supermodularity and Complementarity*, p. 159–160), corrected.
`T ⊆ ℝᵐ`, `{F(t,·) : t ∈ T}` is a family of distribution functions on `ℝⁿ` (probability
measures `μ t`), and `V` is a closed convex cone of real-valued functions on `T` (closed under
pointwise convergence, addition and nonnegative scaling) **containing the constant
functions**. Then `t ↦ ∫_S dF(t,w)` lies in `V` for every (Borel) increasing set `S ⊆ ℝⁿ`
iff `t ↦ ∫ h(w) dF(t,w)` lies in `V` for every (Borel measurable) increasing real-valued `h`
on `ℝⁿ` whose integrals exist.

**Corrections to the retired version.** (1) Without `−1 ∈ V` the forward direction is false
(the accepted disproof: `V` = nonnegative functions), because an increasing `h` is a
nonnegative combination of indicators of increasing sets only after subtracting a constant;
all of the book's cones (increasing, supermodular, convex functions) contain the constants,
and the proof needs it, so it is added as `hVconst`. (2) The `μ t` are now probability
measures, as the book's "distribution functions" are. (3) Sets and functions are Borel
measurable, the standing convention under which `∫_S dF` and `∫ h dF` are defined. -/
theorem closed_convex_cone_characterization_v2 {m n : ℕ} (T : Set (Fin m → ℝ))
    (μ : (Fin m → ℝ) → Measure (Fin n → ℝ))
    (hμprob : ∀ t : T, IsProbabilityMeasure (μ (t : Fin m → ℝ)))
    (V : Set (T → ℝ))
    (hVclosed : IsClosed V)
    (hVadd : ∀ ⦃f g : T → ℝ⦄, f ∈ V → g ∈ V → f + g ∈ V)
    (hVsmul : ∀ ⦃f : T → ℝ⦄, f ∈ V → ∀ ⦃c : ℝ⦄, 0 ≤ c → c • f ∈ V)
    (hVconst : ∀ c : ℝ, (fun _ : T => c) ∈ V) :
    (∀ ⦃S : Set (Fin n → ℝ)⦄, MeasurableSet S → IsUpperSet S →
        (fun t : T => (μ (t : Fin m → ℝ) S).toReal) ∈ V) ↔
      (∀ ⦃h : (Fin n → ℝ) → ℝ⦄, Measurable h → Monotone h →
        (∀ t : T, Integrable h (μ (t : Fin m → ℝ))) →
        (fun t : T => ∫ w, h w ∂ (μ (t : Fin m → ℝ))) ∈ V) := by sorry

end Supermodularity.MDP
