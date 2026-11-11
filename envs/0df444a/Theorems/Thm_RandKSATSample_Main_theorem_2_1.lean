-- Prove2me | Theorems.Thm_RandKSATSample_Main_theorem_2_1
-- name    : RandKSATSample.Main.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:59:19.839196+00:00
-- url     : https://prove2.me/theorems/eb2422ed-e54a-4208-8e7b-ee25edcd7fef
-- title:
--   Theorem 2.1 — Kotecký–Preiss criterion: (2.6) gives absolute convergence of the cluster series, L(w) = log Ξ(w) on the branch with log Ξ(0) = 0, and the pinned bound (2.7)
-- statement:
--   Let $(\mathcal P,\not\sim,w)$ be a polymer model with $\not\sim$ symmetric and reflexive, let $u_\gamma\ge0$ with $|w_\gamma|\le u_\gamma$, and let $A:\mathcal P\to[0,\infty)$ satisfy
--   $$\forall\gamma\in\mathcal P,\qquad\sum_{\gamma'\not\sim\gamma}u_{\gamma'}e^{A(\gamma')}\le A(\gamma)\quad(2.6).$$
--   Then the cluster series $L(w)$ of (2.5) converges absolutely and $L(w)=\log\Xi(w)$, the branch with $\log\Xi(0)=0$; and for every polymer $\gamma_0$,
--   $$\sum_{\ell\ge1}\frac1{(\ell-1)!}\sum_{\gamma_2,\dots,\gamma_\ell\in\mathcal P}|\varphi(\gamma_0,\gamma_2,\dots,\gamma_\ell)|\prod_{i=2}^\ell u_{\gamma_i}\le e^{A(\gamma_0)}\quad(2.7).$$
--   This is the convergence criterion behind the expansion of $\ln Z(\sigma)$ in Lemma 4.3.
--
--   Differences from the source:
--   - reading: L(w) = log Ξ(w), the analytic branch with log Ξ(0) = 0 → exp(L(w)) = Ξ(w) and L is continuous on the polydisc {w' : |w'_γ| ≤ u_γ}; reason: the polydisc is convex and contains 0 where L = 0, and every w' in it satisfies the hypotheses, so a continuous logarithm of Ξ on it vanishing at 0 is unique: this pins the branch
--   - encoding: Σ_{ℓ≥1} (1/ℓ!) Σ_{tuples of length ℓ} (2.5), converging absolutely → tsum over cluster labels ⟨ℓ', Γ : Fin (ℓ'+1) → P⟩ with Summable of the norms; reason: absolute summability of the regrouped family is absolute convergence of the double series and gives the same sum
--   - encoding: the pinned series (2.7), indexed by ℓ ≥ 1 → Summable and tsum of pinnedTerm over ℓ' = ℓ − 1 ≥ 0; reason: the series of nonnegative terms converges and its sum is bounded
--   - encoding: Ξ, φ, incompatibility as part of the model (≁ symmetric, γ ≁ γ) → arbitrary inc with hypotheses hsymm, hrefl; reason: the paper's polymer models are exactly those with these properties
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 9, Theorem 2.1

import Mathlib
import Definitions.Def_RandKSATSample_Main_PolymerModel

set_option autoImplicit false

open Classical

namespace RandKSATSample.Main

/-- Theorem 2.1 (Kotecký–Preiss criterion): for a polymer model with activities `|w_γ| ≤ u_γ`
and a penalty `A ≥ 0` with `Σ_{γ' ≁ γ} u_{γ'} e^{A(γ')} ≤ A(γ)` for every `γ` (2.6), the cluster
series `L(w)` converges absolutely and equals the branch of `log Ξ(w)` with `log Ξ(0) = 0`
(here: `exp L(w) = Ξ(w)` and `L` is continuous on the polydisc `|w'_γ| ≤ u_γ`), and for every
polymer `γ0` the pinned sum (2.7) is at most `e^{A(γ0)}`. -/
theorem theorem_2_1 {P : Type} [Fintype P] (inc : P → P → Prop)
    (hsymm : ∀ γ γ', inc γ γ' → inc γ' γ) (hrefl : ∀ γ, inc γ γ)
    (w : P → ℂ) (u : P → ℝ) (hu : ∀ γ, 0 ≤ u γ) (hwu : ∀ γ, ‖w γ‖ ≤ u γ)
    (A : P → ℝ) (hA : ∀ γ, 0 ≤ A γ)
    (hKP : ∀ γ, ∑ γ' ∈ Finset.univ.filter (fun γ' => inc γ' γ), u γ' * Real.exp (A γ') ≤ A γ) :
    Summable (fun Γ : ClusterLabel P => ‖clusterTerm inc w Γ‖) ∧
    Complex.exp (clusterSeries inc w) = partitionFn inc w ∧
    ContinuousOn (clusterSeries inc) {w' : P → ℂ | ∀ γ, ‖w' γ‖ ≤ u γ} ∧
    ∀ γ0 : P, Summable (pinnedTerm inc u γ0) ∧
      ∑' ℓ' : ℕ, pinnedTerm inc u γ0 ℓ' ≤ Real.exp (A γ0) := by sorry

end RandKSATSample.Main
