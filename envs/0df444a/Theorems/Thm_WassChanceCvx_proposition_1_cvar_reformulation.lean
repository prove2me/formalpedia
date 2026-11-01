-- Prove2me | Theorems.Thm_WassChanceCvx_proposition_1_cvar_reformulation
-- name    : WassChanceCvx.proposition_1_cvar_reformulation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:57.411191+00:00
-- url     : https://prove2.me/theorems/e1f1399b-4cc7-4b6c-a02f-1afbff970966
-- title:
--   Proposition 1 — CVaR reformulation of the pessimistic feasible set $\mathcal X^p$
-- statement:
--   Let $E$ be a finite-dimensional real normed space with its Borel σ-algebra, $\mathbb P$ a Borel probability measure on $E$, $\delta>0$ and $\epsilon\in(0,1)$, and let $A(x)$, $b(x)$ depend affinely on $x\in\mathbb R^n$. Let $\mathcal X^p$ be the feasible region of the pessimistic chance constraint over the type-1 Wasserstein ball of radius $\delta$ around $\mathbb P$, and let $\zeta\sim\mathbb P$. Then for every $x$ whose unsafe set $\mathcal S^c(x)=\{\xi: A(x)\xi\not\le b(x)\}$ is nonempty,
--
--   $$
--   x\in\mathcal X^p\iff \frac\delta\epsilon+\mathrm{CVaR}_{1-\epsilon}\bigl(-d(\zeta,\mathcal S^c(x))\bigr)\le0,
--   $$
--
--   where $d(\zeta,\mathcal S^c(x))=\inf\{\|\zeta-\xi\|:\xi\in\mathcal S^c(x)\}$.
--
--   This turns the robust constraint, an infimum over infinitely many distributions, into one risk constraint under the reference distribution. It is the paper's version of Xie's reformulation, stated for an arbitrary reference distribution.
--
--   **Formalization Note** The CVaR is taken of the law of $\zeta\mapsto-d(\zeta,\mathcal S^c(x))$, a real random variable bounded above by $0$ (the distance is finite because $\mathcal S^c(x)\ne\emptyset$).
--
--   Differences from the source:
--   - encoding: ℝ^q (written ℝ^m in §3.1) with an arbitrary norm ‖·‖; rows $a_i$ with dual norm $\|a_i\|_*$ → a finite-dimensional real normed space $E$ with its Borel σ-algebra; rows are continuous linear functionals on $E$, $\|a_i\|_*$ their operator norm; reason: the same objects: ℝ^q with any norm is such a space and the dual norm is the operator norm
--   - encoding: decision $x\in\mathbb R^n$; $A(x)\in\mathbb R^{m\times q}$ and $b(x)\in\mathbb R^m$ affine in $x$ → `Fin n → ℝ`; `A` an affine map into $k$-tuples of functionals on $E$, `b` an affine map into $\mathbb R^k$; reason: same data; $k$ rows of $A(x)$, each a functional on $E$
--   - reading: $\mathcal P_0$ is the set of all probability distributions; $\Xi$ is the support of $\xi$ → all Borel probability measures on $E$; $\Xi=E$; reason: p.3 takes all probability distributions, and the proof of Theorem 1 (p.8) uses $d(\zeta,\mathcal S^c(x))=(f(x,\zeta))^+$ for every $\zeta\in\mathbb R^m$, which holds only when the unsafe set is taken in all of $\mathbb R^m$
--   - encoding: $\inf_{\mathbb Q\in\mathcal P}\mathbb Q[A(x)\xi\le b(x)]\ge1-\epsilon$ with $\mathcal P=\{\mathbb Q: d_W(\mathbb Q,\mathbb P)\le\delta\}$ → `ENNReal.ofReal (1 - ϵ) ≤ ⨅ ℚ ∈ ambiguityBall δ 1 P univ, ℚ (safeSet …)` in $[0,\infty]$, with $W_1$ valued in $[0,\infty]$; reason: the same condition: all values lie in $[0,1]$ and $1-\epsilon>0$; measures at infinite distance are outside the ball, so no moment condition restricts it
--   - encoding: $1-\epsilon\in(0,1)$, the standing assumption of p.1 → hypotheses `0 < ϵ` and `ϵ < 1`; reason: same range
--   - encoding: the set identity $\mathcal X^p=\{x: \delta/\epsilon+\mathrm{CVaR}_{1-\epsilon}(-d(\zeta,\mathcal S^c(x)))\le0\}$ over all $x\in\mathbb R^n$ → an equivalence for each $x$ with $\mathcal S^c(x)\ne\emptyset$; reason: when $\mathcal S^c(x)=\emptyset$, $d\equiv+\infty$ and the paper's CVaR of the constant $-\infty$ is undefined (and $x\in\mathcal X^p$ trivially)
--   - encoding: VaR and CVaR of a random variable; $\min_\gamma$ in Definition 5 → `VaR` and `CVaR` of its law (`P.map …`); the real infimum `⨅ γ`; reason: both depend only on the law, and the objective is bounded below and attains its minimum when the positive part is integrable and $\epsilon\in(0,1)$
--   - encoding: real distance $d(\zeta,\mathcal S^c(x))$ → `unsafeDist`, `Metric.infEDist` valued in $[0,\infty]$, entering the CVaR through `toReal`; reason: finite when $\mathcal S^c(x)\ne\emptyset$, so `toReal` changes nothing
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Proposition 1 and (2), p.6

import Mathlib
import Definitions.Def_WassChanceCvx_pessimisticSet
import Definitions.Def_WassChanceCvx_unsafeDist
import Definitions.Def_WassChanceCvx_CVaR

open MeasureTheory

namespace WassChanceCvx

/-- **Proposition 1 (CVaR reformulation of (P-CC), adapted from Xie 2019).**
Shen, Jiang, arXiv:2111.02486v2, Proposition 1, p.6: "For `δ > 0`, it holds that
`𝒳^p = {x ∈ ℝⁿ : δ/ϵ + CVaR_{1−ϵ}(−d(ζ, 𝒮ᶜ(x))) ≤ 0}`. (2) Here, random variable `ζ` follows the
reference distribution `ℙ` …"

For every decision `x` whose unsafe set `𝒮ᶜ(x)` is nonempty, `x ∈ 𝒳^p` if and only if
`δ/ϵ + CVaR_{1−ϵ}(−d(ζ, 𝒮ᶜ(x))) ≤ 0`, with `ζ ∼ P`.

**Formalization Note.** General affine `A(x)`, `b(x)` and any Borel probability measure `P` on
`E` (no α-concavity). `Ξ = E`. The set identity is stated pointwise for the `x` with
`𝒮ᶜ(x) ≠ ∅`; for the others `d ≡ +∞`, the paper's `CVaR` of the constant `−∞` is undefined, and
`x ∈ 𝒳^p` holds trivially. For such `x` the distance `d` is finite, and `−d` is a real random
variable bounded above by `0` (`toReal` of a finite value). -/
theorem proposition_1_cvar_reformulation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {n k : ℕ}
    (A : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → StrongDual ℝ E)) (b : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → ℝ))
    (P : Measure E) [IsProbabilityMeasure P] (δ ϵ : ℝ) (hδ : 0 < δ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (x : Fin n → ℝ) (hx : (safeSet (A x) (b x))ᶜ.Nonempty) :
    x ∈ pessimisticSet A b P δ ϵ ↔
      δ / ϵ + CVaR (1 - ϵ) (P.map (fun ζ => -(unsafeDist (A x) (b x) ζ).toReal)) ≤ 0 := by sorry

end WassChanceCvx
