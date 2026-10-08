-- Prove2me | Theorems.Thm_Reiman84_QueueLength_lemma_6
-- name    : Reiman84.QueueLength.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:06:30.382858+00:00
-- url     : https://prove2.me/theorems/0ee75ebf-2720-497f-8820-ed4428988048
-- title:
--   Lemma 6 — tightness of sup₀≤t≤1 Zⁿ_k(t)
-- statement:
--   Consider a sequence of networks of §2 satisfying (20)–(26), let $(Q^n,B^n)$ solve (1)–(3) almost surely, and $Z^n(t)=n^{-1/2}Q^n(nt)$. For each station $1\le k\le K$ and every $\epsilon>0$ there exist $M,N<\infty$ such that
--   $$P^n\Big\{\sup_{0\le t\le1}Z^n_k(t)\ge M\Big\}<\epsilon\qquad\text{for all } n\ge N.$$
--
--   This stochastic boundedness of the scaled queue lengths is used to show that the scaled idleness vanishes (Proposition 4).
--
--   **Formalization Note** The supremum is taken in the extended reals, so it is meaningful whether or not the path is bounded.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), p. 449, Lemma 6

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic

namespace Reiman84.QueueLength

open Filter Topology MeasureTheory

/-- Lemma 6, p. 449: under (20)–(26), for each station `k` and each `ε > 0` there exist
`M, N < ∞` with `Pⁿ{sup_{0≤t≤1} Zⁿ_k(t) ≥ M} < ε` for all `n ≥ N`, where
`Zⁿ(t) = n^{-1/2} Qⁿ(nt)`. -/
theorem lemma_6 {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c)
    (Q B : ∀ n, Ω n → ℝ → Fin K → ℝ)
    (hQ : ∀ n, ∀ᵐ ω ∂(P n), (net n).IsQueueSolution ω (Q n ω) (B n ω)) :
    ∀ k : Fin K, ∀ ε : ℝ, 0 < ε → ∃ (M : ℝ) (N : ℕ), ∀ n, N ≤ n →
      P n {ω | (M : EReal) ≤ ⨆ t ∈ Set.Icc (0 : ℝ) 1, ((diffScale n (Q n ω) t k : ℝ) : EReal)}
        < ENNReal.ofReal ε := by sorry

end Reiman84.QueueLength
