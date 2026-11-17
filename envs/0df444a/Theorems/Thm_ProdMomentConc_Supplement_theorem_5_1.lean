-- Prove2me | Theorems.Thm_ProdMomentConc_Supplement_theorem_5_1
-- name    : ProdMomentConc.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:35:00.976165+00:00
-- url     : https://prove2.me/theorems/b440bf9f-642c-4a8d-aca5-89c1a85a6394
-- title:
--   Theorem 5.1 — spectral product bound $\mathbb E_\varphi[\prod_j f_{i_j}(v_{i_j})]\le\|\varphi\|_{\pi^{-1}}\sqrt\mu\prod_j(\mu+\lambda^{g_j}(1-\mu))$
-- statement:
--   Let $M$ be an ergodic Markov chain on $[n]$ with stationary distribution $\pi$, and let $\lambda=\lambda(M)$ be its $L^2(\pi)$ spectral norm, the operator norm of $M$ on mean-zero functions. Let $(v_1,\dots,v_t)$ be a walk of the chain whose initial state $v_1$ has distribution $\varphi$, and let $f_1,\dots,f_t:[n]\to[0,1]$ have common stationary mean $\mathbb E_\pi f_i=\mu$. Fix times $1\le i_1<\dots<i_k\le t$ and let $g_j=i_{j+1}-i_j$ for $j\in[k-1]$. Then
--   $$\mathbb E_\varphi\Big[\prod_{j=1}^k f_{i_j}(v_{i_j})\Big]\le\|\varphi\|_{\pi^{-1}}\sqrt\mu\prod_{j=1}^{k-1}\big(\mu+\lambda^{g_j}(1-\mu)\big),\qquad \|\varphi\|_{\pi^{-1}}^2=\sum_{v\in[n]}\frac{\varphi(v)^2}{\pi(v)},$$
--   and, if the walk starts from stationarity ($\varphi=\pi$),
--   $$\mathbb E_\pi\Big[\prod_{j=1}^k f_{i_j}(v_{i_j})\Big]\le\mu\prod_{j=1}^{k-1}\big(\mu+\lambda^{g_j}(1-\mu)\big).$$
--
--   This fixed-tuple product-moment bound, in which dependence decays geometrically in the gaps between sampled times, feeds the product-moment tail method for Markov-chain sums (Theorem 5.3 of the paper) after averaging over a random set of times.
--
--   **Formalization Note** The walk expectation, stochastic matrix and stationary law are the published `FiniteTD.Markov.pathExp`, `IsStochastic`, `IsStationaryDist`. Indexing is 0-based: the walk is $w:\mathrm{Fin}(T+1)\to\mathrm{Fin}\,n$ with $t=T+1$, and the paper's $k$ times are $i:\mathrm{Fin}(k+1)\to\mathrm{Fin}(T+1)$.
--
--   Differences from the source:
--   - encoding: walk (v₁, …, v_t), observables f₁, …, f_t, times 1 ≤ i₁ < ⋯ < i_k ≤ t (k ≥ 1) → w : Fin (T+1) → Fin n with t = T+1 and v_s = w (s−1); f : Fin (T+1) → Fin n → ℝ; strictly increasing i : Fin (k+1) → Fin (T+1), so the paper's k is k+1 and the k gaps are i (j+1) − i j; reason: 0-based Lean indexing; the paper's k ≥ 1 is automatic
--   - encoding: E_φ over the walk started from φ → FiniteTD.Markov.pathExp φ M T F = ∑_w φ(w 0) ∏_s M(w s, w (s+1)) F(w); reason: the law of a finite walk of a Markov chain
--   - encoding: M ergodic (irreducible and aperiodic) → IsErgodic M: some power of M has all entries positive, plus FiniteTD.Markov.IsStochastic M; reason: for finite stochastic matrices the two notions coincide
--   - encoding: λ(M) = sup over f ≠ 0, E_π f = 0 of ‖Mf‖_{2,π}/‖f‖_{2,π} → specNorm M π, the sSup of that set of reals; reason: for π of full support the set is bounded; for n ≤ 1 it is empty and the value 0 is the norm of the zero operator
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Theorem 5.1, p.24 (PDF p.24); setting §5, pp.23–24 and §2.4, Definition 2.8, pp.10–11; proof App. C.1, pp.42–43

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_ProdMomentConc_Supplement_SpectralNorm

namespace ProdMomentConc.Supplement

/-- **Theorem 5.1 (spectral product bound for Markov chains).** Saks, Srinivasan, Valieva,
*Concentration from Product Moments via an Additional Element of Randomness*, arXiv:2608.04125
(held version, sha256 5218e9d0…), Theorem 5.1, p.24 (setting pp.23–24, Definition 2.8 p.11; proof
App. C.1, pp.42–43).

Let `M` be an ergodic Markov chain on `[n]` with stationary distribution `π`, `λ = λ(M)` its
`L²(π)` spectral norm, `φ` the initial distribution of `v₁`, and `fᵢ : [n] → [0,1]` with common
stationary mean `E_π fᵢ = µ`. Fix times `1 ≤ i₁ < ⋯ < i_k ≤ t` with gaps `g_j = i_{j+1} − i_j`. Then
`E_φ[∏_{j=1}^k f_{i_j}(v_{i_j})] ≤ ‖φ‖_{π⁻¹} √µ ∏_{j=1}^{k−1} (µ + λ^{g_j}(1 − µ))`, and, if `φ = π`,
`E_π[∏_{j=1}^k f_{i_j}(v_{i_j})] ≤ µ ∏_{j=1}^{k−1} (µ + λ^{g_j}(1 − µ))`.

**Formalization Note.**
* Stochastic matrix, stationary distribution and the expectation over the walk are the published
  `FiniteTD.Markov.IsStochastic`, `IsStationaryDist` and `pathExp`:
  `pathExp φ M T F = ∑_w φ(w₀) ∏_s M(w_s, w_{s+1}) F(w)` over walks `w : Fin (T+1) → Fin n`.
* Indexing is 0-based: the walk `(v₁, …, v_t)` is `w : Fin (T+1) → Fin n` with `t = T + 1` and
  `v_s = w (s − 1)`; the observable `f_s` is `f ⟨s − 1⟩`.
* The paper's `k` sampled times are `i : Fin (k+1) → Fin (T+1)` (so the paper's `k` is `k + 1` here,
  and `k + 1 ≥ 1` is automatic), strictly increasing; the `k` gaps are
  `g_j = i (j+1) − i j` (natural numbers, positive by strict monotonicity).
* `λ(M)` is `specNorm M π` (Definition 2.8: the operator norm on mean-zero functions in `L²(π)`,
  no reversibility), `‖φ‖_{π⁻¹}` is `piInvNorm π φ`, ergodicity is `IsErgodic` (primitivity). -/
theorem theorem_5_1 {n : ℕ} (M : Fin n → Fin n → ℝ) (hM : FiniteTD.Markov.IsStochastic M)
    (hErg : IsErgodic M) (π : Fin n → ℝ) (hπ : FiniteTD.Markov.IsStationaryDist M π)
    (φ : Fin n → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∑ x, φ x = 1)
    (T : ℕ) (f : Fin (T + 1) → Fin n → ℝ) (hf : ∀ s x, 0 ≤ f s x ∧ f s x ≤ 1)
    (μ₀ : ℝ) (hmean : ∀ s, piMean π (f s) = μ₀)
    (k : ℕ) (i : Fin (k + 1) → Fin (T + 1)) (hi : StrictMono i) :
    FiniteTD.Markov.pathExp φ M T (fun w => ∏ j : Fin (k + 1), f (i j) (w (i j))) ≤
      piInvNorm π φ * Real.sqrt μ₀ *
        ∏ j : Fin k, (μ₀ + specNorm M π ^ ((i j.succ : ℕ) - (i j.castSucc : ℕ)) * (1 - μ₀)) ∧
    FiniteTD.Markov.pathExp π M T (fun w => ∏ j : Fin (k + 1), f (i j) (w (i j))) ≤
      μ₀ * ∏ j : Fin k, (μ₀ + specNorm M π ^ ((i j.succ : ℕ) - (i j.castSucc : ℕ)) * (1 - μ₀)) := by sorry

end ProdMomentConc.Supplement
