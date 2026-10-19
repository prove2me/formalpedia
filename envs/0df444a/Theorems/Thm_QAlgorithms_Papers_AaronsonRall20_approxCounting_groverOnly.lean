-- Prove2me | Theorems.Thm_QAlgorithms_Papers_AaronsonRall20_approxCounting_groverOnly
-- name    : QAlgorithms.Papers.AaronsonRall20.approxCounting_groverOnly
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:10:50.761089+00:00
-- url     : https://prove2.me/theorems/2a1f72e5-91cf-4143-9d79-bae87aa55c05
-- title:
--   Aaronson–Rall Theorem 1: approximate counting with Grover iterations only
-- statement:
--   This is the main theorem of Aaronson and Rall: approximate counting with the optimal query complexity, using Grover iterations only (no quantum Fourier transform).
--
--   Let $S\subseteq[N]$ be a nonempty set of marked items and $K=|S|$. The algorithm (AR p.4) pads the list with $10^6N$ unmarked items, giving $N'=(10^6+1)N$ items. Let $U|x\rangle=(-1)^{[x\in S]}|x\rangle$ be the membership (phase) oracle, $|\psi\rangle$ the uniform superposition over the $N'$ items, and $G=(I-2|\psi\rangle\langle\psi|)U$. The only quantum operation is: prepare $G^{(r-1)/2}|\psi\rangle$ for an odd $r$ and measure it in the computational basis, at a cost of $(r-1)/2$ queries.
--
--   1. Step 1: for $k=0,1,2,\dots$, take $r_k$ to be the largest odd integer $\le 1.05^k$. Run $\lceil 5000\ln(5/\delta)\rceil$ shots, and stop at the first $k=k_{\mathrm{end}}$ at which at least $95\%$ of the shots return a marked item.
--   2. Step 2: start from $\theta_{\min}=0.9\cdot1.05^{-k_{\mathrm{end}}}$ and $\theta_{\max}=1.65\,\theta_{\min}$. In round $t$, choose $r_t$ by the rotation lemma (eqs. (45)–(47)) and run $\lceil 250\ln(1/\delta_t)\rceil$ shots, where $\delta_t=(\delta\varepsilon/65)\,0.9^{-t}$. With $\gamma=\theta_{\max}/\theta_{\min}-1$: if at least $12\%$ of the shots are marked, set $\theta_{\min}:=\theta_{\max}/(1+0.9\gamma)$; otherwise set $\theta_{\max}:=(1+0.9\gamma)\theta_{\min}$. Stop as soon as $\theta_{\max}\le(1+\varepsilon/5)\theta_{\min}$.
--   3. Output $\hat K=N'\sin^2(\theta_{\max})$.
--
--   The theorem has three parts.
--
--   1. There is a function $Q(N,K,\varepsilon,\delta)$ and constants $C>0$, $\varepsilon_0>0$, $\delta_0\in(0,1)$ such that for all $1\le K\le N$, all $\varepsilon\in(0,\varepsilon_0]$ and all $\delta\in(0,\delta_0]$,
--   $$Q(N,K,\varepsilon,\delta)\le C\sqrt{N/K}\,\varepsilon^{-1}\ln(1/\delta).$$
--   2. For every $N$, every nonempty $S$ and all $\varepsilon,\delta>0$,
--   $$\Pr\big[\,K(1-\varepsilon)<\hat K<K(1+\varepsilon)\ \text{ and the run makes fewer than } Q(N,K,\varepsilon,\delta) \text{ queries}\,\big]\ge 1-\delta.$$
--   3. The register of the algorithm, $[N']$, needs $\lceil\log_2 N'\rceil=O(\log N)$ qubits.
--
--   The function $Q$ and the constants are fixed before $N$, $S$, $\varepsilon$ and $\delta$. The result matches the BHMT query complexity $O(\varepsilon^{-1}\sqrt{N/K})$ for approximate counting, and it is the basis of QFT-free amplitude estimation.
--
--   **Formalization Note** The theorem is stated for the paper's concrete algorithm (the frozen definitions `acEventProb`, `acStep1Exit`, `acStep2`), with every shot count "at least $m$" taken as exactly $\lceil m\rceil$ and Mathlib's `round` used for the rotation lemma's roundings (the paper allows any tie-breaking). The sentence "fewer than $Q$ queries whenever the estimate is accurate" is formalized as the joint event of accuracy and fewer than $Q$ queries, which is what the proof establishes. That event implies the accuracy claim. The $O$-bound is uniform in $N$ and $K$ as $\varepsilon,\delta\to0$.
-- source:
--   Quantum Approximate Counting, Simplified (Aaronson, Rall), arXiv:1908.10846v6, Theorem 1, PDF p. 4. https://arxiv.org/abs/1908.10846v6 . PDF SHA-256: 543f3bf54cab66cf214ae8f993b3cbac64513aff238943f89ebe279c12d451c5.

import Definitions.Def_QAlgorithms_Defs_ApproxCounting
set_option autoImplicit false

namespace QAlgorithms.Papers.AaronsonRall20

open QAlgorithms
open scoped ENNReal

/-- AR p.4, Theorem 1 (approximate counting with Grover iterations only).

For the paper's algorithm on a nonempty marked set `S ⊆ [N]`, `K = |S|`, and any `ε, δ > 0`:
with probability at least `1 − δ` the output `K̂` satisfies `K(1 − ε) < K̂ < K(1 + ε)` and the
run made fewer than `Q(N, K, ε, δ)` queries, where `Q ∈ O(√(N/K) ε⁻¹ log δ⁻¹)` (as
`ε, δ → 0`, uniformly in `N` and `K`). The algorithm's register is the padded list
`[(10⁶ + 1) N]`, i.e. `O(log N)` qubits. -/
theorem approxCounting_groverOnly :
    ∃ Q : ℕ → ℕ → ℝ → ℝ → ℝ,
      (∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧
        ∀ N K : ℕ, 1 ≤ K → K ≤ N → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          Q N K ε δ ≤ C * Real.sqrt ((N : ℝ) / (K : ℝ)) * ε⁻¹ * Real.log δ⁻¹) ∧
      (∀ (N : ℕ) (S : Finset (Fin N)), S.Nonempty → ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        ENNReal.ofReal (1 - δ) ≤ acEventProb S ε δ fun Khat q =>
          (S.card : ℝ) * (1 - ε) < Khat ∧ Khat < (S.card : ℝ) * (1 + ε) ∧
            (q : ℝ) < Q N S.card ε δ) ∧
      ∃ C : ℕ, ∀ N : ℕ, 2 ≤ N → Nat.clog 2 (acPadLen N) ≤ C * Nat.log 2 N := by
  sorry

end QAlgorithms.Papers.AaronsonRall20
