-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_Supplement_expansionRate_eq_sInf_lyapunovExponent
-- name    : StochApproxDyn.WeakAPT.Supplement.expansionRate_eq_sInf_lyapunovExponent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:15:54.287387+00:00
-- url     : https://prove2.me/theorems/6dca3588-ee2c-4e56-a797-7d091de8166c
-- title:
--   Theorem 8.12 — the expansion rate at a compact positively invariant set is the infimum of the smallest Lyapounov exponents of its ergodic measures (Schreiber)
-- statement:
--   Let $M$ be a Riemannian manifold (Hausdorff, second countable, without boundary, with a continuous Riemannian metric) and $\Phi$ a $C^1$ flow on $M$, so that $(t,x)\mapsto\Phi_t(x)$ is $C^1$. For $K\subseteq M$ write $EC(\Phi_t,K)=\inf_{x\in K}m(D\Phi_t(x))$, where $m(L)=\inf_{\|v\|=1}\|Lv\|$ is the minimal norm. For an ergodic invariant probability measure $\mu$, $\lambda_1(\mu)$ is its smallest Lyapounov exponent, the $\mu$-almost sure value of $\lim_{t\to\infty}\frac1t\log m(D\Phi_t(x))$.
--
--   Let $K\subseteq M$ be a compact positively invariant set ($\Phi_t(K)\subseteq K$ for $t\ge0$). Then the expansion rate exists and
--
--   $$\mathcal E(\Phi,K)=\lim_{t\to\infty}\frac1t\log EC(\Phi_t,K)=\inf_\mu\lambda_1(\mu),$$
--
--   where the infimum is over all ergodic invariant probability measures of the flow with support in $K$.
--
--   This ergodic characterization of the expansion rate, due to Schreiber (1997), is what makes the shadowing condition of Theorem 8.9 checkable: it reduces $\mathcal E(\Phi,K)$ to exponents at equilibria, periodic orbits and other ergodic measures (Corollaries 8.13–8.15).
--
--   **Formalization Note** Both sides are extended reals: the logarithm of $EC\in[0,\infty]$ is computed in $[-\infty,\infty]$, and $K=\emptyset$ gives $+\infty$ on both sides. Invariance is $(\Phi_t)_*\mu=\mu$ for $t\ge0$, which for a flow is invariance for all $t\in\mathbb R$; ergodicity is with respect to sets invariant under the whole flow, not only under $\Phi_1$. Support in $K$ is $\mu(M\setminus K)=0$, the same as $\operatorname{supp}\mu\subseteq K$ since $K$ is closed.
--
--   Differences from the source:
--   - generalization: "we furthermore assume without loss of generality that $M$ is compact" (p. 43) → $M$ need not be compact; reason: the statement involves $\Phi$ only through $D\Phi_t$ on $K$ and measures supported in $K$, and compact $M$ is a special case.
--   - reading: the limit defining $\mathcal E(\Phi,K)$ "exists by a standard subadditivity argument … left to the reader" (p. 40) → its existence is part of the conclusion; reason: the theorem's left side is that limit.
--   - reading: "Riemannian manifold", "$C^1$ flow" → Hausdorff, second countable, boundaryless $C^1$ manifold with a continuous Riemannian metric, and $(t,x)\mapsto\Phi_t(x)$ jointly $C^1$; reason: the usual meaning of these terms.
--   - encoding: $\lambda_1(\mu)$ via the Oseledec splitting → the $\mu$-a.e. limit of $\frac1t\log m(D\Phi_t(x))$; reason: by Oseledec's theorem this limit is the smallest exponent, so the set of values is $\{\lambda_1(\mu)\}$.
--   - encoding: real values → extended reals, support in $K$ as $\mu(M\setminus K)=0$; reason: Lean conventions; same instances, and $K=\emptyset$ gives $+\infty=\inf\emptyset$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 44, Theorem 8.12 (expansion constant and rate, §8.2, p. 40; invariant and ergodic measures, §8.3, p. 43; Lyapounov exponents, p. 44)

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_InvariantMeasures
import Definitions.Def_StochApproxDyn_WeakAPT_Supplement_ExpansionRate

open scoped NNReal ENNReal Manifold
open Bundle MeasureTheory Filter

namespace StochApproxDyn.WeakAPT.Supplement

/-- Theorem 8.12 (Benaïm 1999, p. 44; due to Schreiber 1997). Let `Φ` be a `C¹` flow on a
Riemannian manifold `M` (§8.2, p. 40) and `K ⊆ M` a compact positively invariant set. Then the
expansion rate `ℰ(Φ, K) = lim_{t → ∞} (1/t) log EC(Φ_t, K)` exists and equals
`inf_μ λ₁(μ)`, the infimum of the smallest Lyapounov exponent over all ergodic (continuous-time)
invariant probability measures `μ` with support in `K`. Both sides are taken in `EReal`, so that
`K = ∅` gives `+∞ = inf ∅`. -/
theorem expansionRate_eq_sInf_lyapunovExponent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [MeasurableSpace M] [BorelSpace M]
    (Φ : Flow ℝ M) (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I 1 (fun p : ℝ × M => Φ p.1 p.2))
    (K : Set M) (hK : IsCompact K) (hKinv : ∀ t : ℝ, 0 ≤ t → Φ t '' K ⊆ K) :
    Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * ENNReal.log (expansionConstant I Φ K t)) atTop
      (nhds (sInf {lam : EReal | ∃ μ : ProbabilityMeasure M,
        IsErgodicSupportedIn Φ K μ ∧ IsSmallestLyapunovExponent I Φ μ lam})) := by sorry

end StochApproxDyn.WeakAPT.Supplement
