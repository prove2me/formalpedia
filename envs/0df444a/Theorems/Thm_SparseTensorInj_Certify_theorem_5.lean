-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_theorem_5
-- name    : SparseTensorInj.Certify.theorem_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:39:17.20543+00:00
-- url     : https://prove2.me/theorems/e0052502-dabc-4bc5-b3e4-737b2ca62e0f
-- title:
--   Theorem 5 — a polynomial-time certificate for the injective norm of random subgaussian tensors with leading term $\sigma n^{k/4}$
-- statement:
--   Fix an integer $k\ge2$ and let $u_k$ be the paper's certificate: $u_k(T)=\|A(T)\|_{\mathrm{op}}$ (Definition 37) for even $k$ and the quantity (9) for odd $k$. Then:
--
--   1. (correctness) $\|T\|_{\mathrm{inj}}\le u_k(T)$ for every $n$ and every symmetric order-$k$ tensor $T$ over $\mathbb R^n$;
--   2. (utility) there are $C_k>0$ and $\delta:\mathbb N\to\mathbb R$ with $\delta(n)\to0$, depending only on $k$, such that for every $n\ge k$, every $\sigma,\gamma>0$ and every family $\{\chi_e\}_{e\in[n]_k}$ of independent (not necessarily identically distributed) random variables with $\mathbb E\chi_e=0$, $\mathbb E\chi_e^2\le\sigma^2$, $\|\chi_e\|_{\psi_2}\le\gamma$, the random tensor $T$ of Definition 3 satisfies $\Pr[u_k(T)>C_k\,b_k(n,\sigma,\gamma)]\le\delta(n)$, where
--   $$b_k(n,\sigma,\gamma)=\begin{cases}\sigma n^{k/4}+\gamma\sqrt{\log(1+\gamma^2/\sigma^2)}\cdot\sqrt{\log n}&k\text{ even},\\ \sigma n^{k/4}+\gamma\sqrt{\log(1+\gamma^2/\sigma^2)}\cdot(\log n)^{k/4}&k\text{ odd}.\end{cases}$$
--
--   So $u_k$ is a certification algorithm in the sense of Definition 4 with utility $C_kb_k$. The leading term $\sigma n^{k/4}$ depends on the variance $\sigma^2$ only, which for sparse entries is much smaller than the subgaussian parameter $\gamma^2$. Propositions 36 and 44 are its two parity cases.
--
--   Differences from the source:
--
--   - reading: there exists a polynomial-time certification algorithm → the paper's explicit certificate (‖A(T)‖_op of Definition 37 for even order, eq. (9) for odd order) is correct for every symmetric tensor and has the stated utility; reason: running time is not modelled; an existential certificate without a running-time bound is trivial (u = ‖T‖_inj); the paper proves this certificate polynomial-time computable (p. 24, p. 54)
--   - reading: with probability 1 − o_n(1) (with high probability), C_k > 0 depending only on k → ∃ C > 0, ∃ δ : ℕ → ℝ with δ n → 0, both chosen before n, σ, γ, the probability space and the law of χ, such that P{C · b < u(T)} ≤ δ n for every n ≥ k; reason: the uniform reading is the stronger one; the paper uses it (Corollary 8 takes p = p(n)) and proves it (failure probability O_q(n^{-3}), resp. n^{-5} + n^{-6}, independent of σ, γ and the law)
--   - reading: the constant (2q + 1)!/2q! in eq. (9) → (2q+1)!/(2·q!); reason: the proof of Lemma 48 (p. 27) derives exactly this constant (‖z‖² ≤ 1/q!); the (2q)! reading changes the certificate for q ≥ 2
--   - encoding: u_k for order-k tensors, by parity of k → certificate k n T: evenCert / oddCert at q = ⌊k/2⌋ after re-indexing along k = q + q or k = 2q + 1 (Fin.cast); parity tested by k % 2 = 0; reason: same certificate
--   - encoding: a fixed natural order ≺ on [n], with J_e, K_e read off the ≺-increasing ordering of e → the order of Fin n; J_e, K_e are the images of positions 1..q and q+1..2q under Finset.orderEmbOfFin; reason: the natural order of [n]
--   - encoding: ‖T‖_inj = max over unit vectors x of |⟨T, x^{⊗k}⟩| → the real supremum ⨆ over {x : Fin n → ℝ | Σ x_i² = 1}; reason: the set of values is bounded and the maximum is attained for n ≥ 1; for n = 0 (empty sphere) the value is 0 and the claim is trivial
--   - encoding: indices in [n] = {1,…,n}; the k-element subsets [n]_k → Fin n (0-based); KSubset n k = {e : Finset (Fin n) // e.card = k}; reason: relabelling of the index set; same instances
--   - encoding: ‖χ‖_ψ2 ≤ γ, with ‖χ‖_ψ2 = inf{t > 0 : E exp(χ²/t²) ≤ 2} → Psi2Le P χ γ: exp(χ²/γ²) is integrable and E exp(χ²/γ²) ≤ 2 (with γ > 0); reason: for γ > 0 the two are equivalent: t ↦ E exp(χ²/t²) is non-increasing and right-continuous by monotone convergence
--   - encoding: random variables on an unspecified probability space → every probability space (Ω : Type, P) with IsProbabilityMeasure P; reason: any joint law of finitely many real variables is realized on such a space; Lean universe convention
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 4, Theorem 5 (proved by Proposition 36, p. 24, and Proposition 44, pp. 52–54)

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_RandomModel
import Definitions.Def_SparseTensorInj_Certify_Certificate

open MeasureTheory ProbabilityTheory Filter Topology

namespace SparseTensorInj.Certify

/-- Theorem 5 (p. 4): fix an integer `k ≥ 2`. The paper's certificate `u_k` (Definition 37 for
even `k`, eq. (9) for odd `k`) is correct, `‖T‖_inj ≤ u_k(T)` for every `n` and every symmetric
order-`k` tensor `T`, and has utility `C_k · b_k`: there are `C_k > 0` and `δ_n → 0`, depending
only on `k`, such that for every `n ≥ k`, every `σ, γ > 0` and every coefficient family of
Definition 3 (independent, not necessarily identically distributed),
`Pr[u_k(T) > C_k b_k(n, σ, γ)] ≤ δ_n`, where `b_k = σ n^{k/4} + γ √(log(1 + γ^2/σ^2)) √(log n)`
for even `k` and `σ n^{k/4} + γ √(log(1 + γ^2/σ^2)) (log n)^{k/4}` for odd `k`. -/
theorem theorem_5 (k : ℕ) (hk : 2 ≤ k) :
    (∀ (n : ℕ) (T : Tensor k n), IsSymmetric T → injNorm T ≤ certificate k n T) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ (n : ℕ), k ≤ n →
      ∀ (σ γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (χ : KSubset n k → Ω → ℝ),
        IsSubgaussianFamily P χ σ γ →
        P {ω | C * utilityBound k n σ γ < certificate k n (modelTensor χ ω)} ≤
          ENNReal.ofReal (δ n) := by sorry

end SparseTensorInj.Certify
