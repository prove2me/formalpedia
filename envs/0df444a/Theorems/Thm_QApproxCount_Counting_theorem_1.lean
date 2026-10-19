-- Prove2me | Theorems.Thm_QApproxCount_Counting_theorem_1
-- name    : QApproxCount.Counting.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:35.434736+00:00
-- url     : https://prove2.me/theorems/8dba0cbf-cb7d-4717-b720-6444ee110033
-- title:
--   Theorem 1 (Approximate Counting) — K(1 − ε) < K̂ < K(1 + ε) with probability ≥ 1 − δ, and < C√(N/K)ε⁻¹log(1/δ) queries on every accurate run
-- statement:
--   Let $S\subseteq[N]$ be a nonempty set of marked items and $K=|S|$. Let $\mathcal A(N,S,\varepsilon,\delta,F)$ be the Approximate Counting algorithm of the algorithm box, which accesses $S$ only through its membership oracle and runs each of its two loops for at most $F$ rounds.
--
--   1. **Accuracy.** For all $0<\varepsilon<1$ and $0<\delta<1$ there is an $F$ such that
--   $$\Pr\big[\mathcal A(N,S,\varepsilon,\delta,F)\text{ outputs }\hat K\text{ with }K(1-\varepsilon)<\hat K<K(1+\varepsilon)\big]\ \ge\ 1-\delta .$$
--   2. **Query complexity.** There is an absolute constant $C$ such that, for all $N$, nonempty $S$, $0<\varepsilon\le1/2$, $0<\delta\le1/2$ and every $F$, every run of $\mathcal A(N,S,\varepsilon,\delta,F)$ that outputs an estimate $\hat K$ with $K(1-\varepsilon)<\hat K<K(1+\varepsilon)$ has made fewer than
--   $$C\,\sqrt{N/K}\;\varepsilon^{-1}\ln(\delta^{-1})$$
--   oracle queries.
--
--   This is the main theorem of the paper: approximate counting with the optimal query complexity using only Grover iterations and classical post-processing, with no quantum Fourier transform.
--
--   **Formalization Note** The algorithm is the defined `approxCount` (padding to $N'=(10^6+1)N$ included), not an existentially quantified one. Fuel exhaustion counts as failure. The paper's $Q(N,K,\varepsilon,\delta)\in O(\sqrt{N/K}\,\varepsilon^{-1}\log\delta^{-1})$ is pinned to $C\sqrt{N/K}\,\varepsilon^{-1}\ln\delta^{-1}$ with one constant $C$ chosen before all other quantities, in the regime $\varepsilon,\delta\le1/2$, where $\ln\delta^{-1}\ge\ln2>0$. The clause about $O(\log N)$ qubits of space is not formalized, because there is no circuit model.
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, p. 4, Theorem 1 (proof pp. 4–8)

import Mathlib
import Definitions.Def_QApproxCount_Counting_Grover
import Definitions.Def_QApproxCount_Counting_Algorithm

namespace QApproxCount.Counting

/-- Theorem 1, p. 4 (Approximate Counting), for the algorithm `approxCount` of the algorithm box.
Let `S ⊆ [N]` be nonempty and `K = |S|`.

(a) For `0 < ε < 1` and `0 < δ < 1` there is a fuel bound `F` such that, with probability at
least `1 - δ`, `approxCount N S ε δ F` halts with an estimate `K̂` satisfying
`K(1 - ε) < K̂ < K(1 + ε)`.

(b) There is an absolute constant `C` such that for all `N`, nonempty `S`, `0 < ε ≤ 1/2`,
`0 < δ ≤ 1/2` and every fuel `F`, every run that halts with an accurate estimate
(`K(1 - ε) < K̂ < K(1 + ε)`) has made fewer than `C · √(N/K) · ε⁻¹ · ln(δ⁻¹)` oracle queries. -/
theorem theorem_1 :
    (∀ (N : ℕ) (S : Finset (Fin N)), S.Nonempty →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ∃ F : ℕ, ENNReal.ofReal (1 - δ) ≤
          (approxCount N S ε δ F).toOuterMeasure
            {o : Option (ℝ × ℕ) | ∃ (Kh : ℝ) (q : ℕ), o = some (Kh, q) ∧
              (S.card : ℝ) * (1 - ε) < Kh ∧ Kh < (S.card : ℝ) * (1 + ε)}) ∧
    (∃ C : ℝ, ∀ (N : ℕ) (S : Finset (Fin N)), S.Nonempty →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
        ∀ (F : ℕ) (Kh : ℝ) (q : ℕ), some (Kh, q) ∈ (approxCount N S ε δ F).support →
          (S.card : ℝ) * (1 - ε) < Kh → Kh < (S.card : ℝ) * (1 + ε) →
            (q : ℝ) < C * Real.sqrt ((N : ℝ) / S.card) * ε⁻¹ * Real.log δ⁻¹) := by sorry

end QApproxCount.Counting
