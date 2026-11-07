-- Prove2me | Theorems.Thm_RGGDetect_theorem_4
-- name    : RGGDetect.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:57.953323+00:00
-- url     : https://prove2.me/theorems/dae0d2ce-3e54-448e-ab7f-e1d0fa2c1ce2
-- title:
--   Theorem 4 — harmonic expansion of $\eta_k$ with bounds (18)–(20)
-- statement:
--   Fix integers $K\ge3$ and $M\ge1$. For every $2\le k<K$, $\eta_k$ of (4) has the orthogonal expansion
--
--   $$
--   \eta_k=\sum_{q=\lceil k/2\rceil}^M\sum_{\mathbf a\in\mathcal A_{k,q}}\gamma_{\mathbf a}D_{\mathbf a}+R_{k,M} \tag{17}
--   $$
--
--   with $D_{\mathbf a}\in\mathcal H_{\mathbf a}$. There are constants $C_0,C_{K,M}>0$ such that if $d\ge3$ and $0<p\le e^{-1}$, then for each multidegree $\mathbf a$ with $\|\mathbf a\|_1=2q\le2M$,
--
--   $$
--   |\gamma_{\mathbf a}|^2\le C_{K,M}\,p^kL^{2q},\qquad\mathbb E[(D_{\mathbf a})^2]\le\frac{C_{K,M}}{d^q}. \tag{18}
--   $$
--
--   The only contribution to (17) from $q=1$ is $k=2$, $\mathbf a=(1,1)$, $D_{(1,1)}(x_1,x_2)=\langle x_1,x_2\rangle$ (19). If in addition $d\ge C_0L^2$, the remainders satisfy
--
--   $$
--   \mathbb E[(R_{k,M})^2]\le C_{K,M}\frac{p^kL^{2M+2}}{d^{M+1}}, \tag{20}
--   $$
--
--   the expectation over independent uniform $x_1,\dots,x_k$.
--
--   **Formalization Note** $D_{\mathbf a}$ is (143), $\gamma_{\mathbf a}$ is (56) with $h=0$, and $R_{k,M}$ is $\eta_k$ minus the main term, so (17) holds by definition; "orthogonal" is stated as $L^2$-orthogonality of $R_{k,M}$ to every $\mathcal H_{\mathbf a}$ with $\mathbf a$ positive and $\|\mathbf a\|_1\le2M$ (this part for $d\ge2$, $0<p<1$). (19) is stated as $\mathcal A_{2,1}=\{(1,1)\}$, $\mathcal A_{k,1}=\varnothing$ for $k\ge3$, and $D_{(1,1)}=\langle x_1,x_2\rangle$ for every $d\ge1$.
--
--   Differences from the source:
--   - encoding: D_a ∈ H_a, γ_a, R_{k,M} in (17) → D_a := (143), γ_a := (56) with h = 0, R_{k,M} := η_k − main term; reason: the paper's explicit objects (p.40); Theorem 5 is not scale invariant, so D_a cannot be existential
--   - encoding: 'orthogonal expansion' → L²-orthogonality of R_{k,M} to every H_a with a positive, ‖a‖₁ ≤ 2M, for d ≥ 2 and 0 < p < 1; reason: the paper's meaning (p.40: the main term is the projection onto ⊕ H_a, ‖a‖₁ ≤ 2M); P_{ℓ,d} needs d ≥ 2, κ needs 0 < p < 1
--   - encoding: (19) 'the only contribution from q = 1' → A_{2,1} = {(1,1)}, A_{k,1} = ∅ for k ≥ 3, D_{(1,1)} = ⟨x₁, x₂⟩ for every d ≥ 1; reason: only k = 2 has ⌈k/2⌉ ≤ 1; the identity holds in every dimension
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Theorem 4, eqs. (17)–(20), pp.7–8 (PDF pp.9–10)

import Mathlib
import Definitions.Def_RGGDetect_harmCoef

open MeasureTheory

namespace RGGDetect

/-- **Theorem 4** (harmonic expansion of `η_k`; arXiv:2610.08517, held version, sha256 e7bebd4a…,
Theorem 4, pp.7–8, eqs. (17)–(20)): fix integers `K ≥ 3`, `M ≥ 1`. For every `2 ≤ k < K`, `η_k` has the
orthogonal expansion `η_k = ∑_{q=⌈k/2⌉}^{M} ∑_{a ∈ A_{k,q}} γ_a D_a + R_{k,M}` (17) with `D_a ∈ H_a`.
There are constants `C₀, C_{K,M} > 0` such that if `d ≥ 3` and `0 < p ≤ e^{-1}`, then for each
multidegree `a` with `‖a‖₁ = 2q ≤ 2M`, `|γ_a|² ≤ C_{K,M} p^k L^{2q}` and `E[(D_a)²] ≤ C_{K,M}/d^q` (18).
The only contribution to (17) from `q = 1` is `k = 2`, `a = (1, 1)`, `D_{(1,1)}(x₁, x₂) = ⟨x₁, x₂⟩`
(19). If in addition `d ≥ C₀L²`, then `E[(R_{k,M})²] ≤ C_{K,M} p^k L^{2M+2}/d^{M+1}` (20), the expectation
over `x₁, …, x_k` independent and uniform.

**Formalization Note** `D_a` is (143), `γ_a` is (56) with `h = 0`, and `R_{k,M}` is `η_k` minus the
main term (`remK`), so (17) holds by definition; "orthogonal" is the third conjunct of the first part:
`R_{k,M}` is `L²`-orthogonal to every `H_a`, `a` positive with `‖a‖₁ ≤ 2M`. The first part needs only
`d ≥ 2` and `0 < p < 1`. `p = capProb d τ`, `L = log(1/p)`. Clause (19) is stated as
`A_{2,1} = {(1,1)}`, `A_{k,1} = ∅` for `k ≥ 3` (only `k = 2` has `⌈k/2⌉ ≤ 1`), and the formula for
`D_{(1,1)}` (for every `d ≥ 1`). -/
theorem theorem_4 (K M : ℕ) (hK : 3 ≤ K) (hM : 1 ≤ M) :
    (∀ d : ℕ, 2 ≤ d → ∀ τ : ℝ, 0 < capProb d τ → capProb d τ < 1 → ∀ k : ℕ, 2 ≤ k → k < K →
      (∀ q : ℕ, ∀ a ∈ Akq k q, (Da (d := d) a) ∈ tensorHarm Finset.univ a) ∧
      (∀ x : Fin k → Sph d, eta d τ k x =
        ∑ q ∈ Finset.Icc ((k + 1) / 2) M, ∑ a ∈ Akq k q, gammaA d τ a * Da a x +
          remK d τ k M x) ∧
      (∀ a : Fin k → ℕ, (∀ j, 1 ≤ a j) → ∑ j, a j ≤ 2 * M →
        ∀ F : (Fin k → Sph d) → ℝ, F ∈ tensorHarm Finset.univ a →
          ∫ x, remK d τ k M x * F x ∂(prior k d) = 0)) ∧
    (∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧ ∀ d : ℕ, 3 ≤ d → ∀ τ : ℝ, 0 < capProb d τ →
      capProb d τ ≤ Real.exp (-1) → ∀ k : ℕ, 2 ≤ k → k < K →
      (∀ q : ℕ, q ≤ M → ∀ a ∈ Akq k q,
        |gammaA d τ a| ^ 2 ≤ C * capProb d τ ^ k * Real.log (1 / capProb d τ) ^ (2 * q) ∧
        ∫ x, Da a x ^ 2 ∂(prior k d) ≤ C / (d : ℝ) ^ q) ∧
      (C₀ * Real.log (1 / capProb d τ) ^ 2 ≤ d →
        ∫ x, remK d τ k M x ^ 2 ∂(prior k d) ≤
          C * capProb d τ ^ k * Real.log (1 / capProb d τ) ^ (2 * M + 2) / (d : ℝ) ^ (M + 1))) ∧
    (Akq 2 1 = {![1, 1]} ∧ (∀ k : ℕ, 3 ≤ k → Akq k 1 = ∅) ∧
      ∀ d : ℕ, 1 ≤ d → ∀ x : Fin 2 → Sph d, Da ![1, 1] x = ip (x 0) (x 1)) := by sorry

end RGGDetect
