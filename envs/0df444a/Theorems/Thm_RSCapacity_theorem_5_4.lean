-- Prove2me | Theorems.Thm_RSCapacity_theorem_5_4
-- name    : RSCapacity.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:47.942863+00:00
-- url     : https://prove2.me/theorems/d3de7478-4f49-43d9-9253-c5dce87a0e6e
-- title:
--   Theorem 5.4 (Prime-field sparse list recovery)
-- statement:
--   Fix $\vartheta\in(0,1)$. There are constants $r_0,a_\vartheta>0$ (and $c$) depending on $\vartheta$ only with the following property. Let $q$ be prime, $\alpha_1,\dots,\alpha_n\in\mathbb F_q$ distinct, and $S_i\subseteq\mathbb F_q$ of total incidence $M$. Let $A,k,K$ be integers with $1\le A\le n$, $1\le k\le K$ and $K\ge2$, and suppose
--   $$\frac{A}{K-1}\ge\frac1{1-\vartheta},\qquad r_0\le r<K,\qquad M\le a_\vartheta(K-1)\frac{r^\vartheta}{\log^4(er)},$$
--   $$B=\Bigl\lceil\frac{r^3A}{K-1}\Bigr\rceil<q,\qquad r^3A<q^2 .$$
--   Then a deterministic algorithm outputs every $P\in\mathbb F_q[X]$ with $\deg P<k$ and at least $A$ list hits, using $q^{O_\vartheta(r)}$ field operations, and the output list has size at most $q^{4r+6}$.
--
--   In the formal statement the algorithm is one coin-free program of the algebraic RAM, chosen after $\vartheta$, which outputs exactly $\mathcal L(D,k,\mathbf S,A)$ within $q^{cr}$ steps.
--
--   Differences from the source:
--   - reading: a deterministic algorithm … using q^{O_ϑ(r)} field operations → the published algebraic RAM over ZMod q (MatroidSensOracle.aexec), one coin-free program, steps counting every instruction, halting within the bound for every word length w with bound < 2^w; the bound is q^{c·r} with c chosen after ϑ; reason: field operations are at most the step count
--   - reading: outputs every P with deg P < k and at least A list hits → outputs exactly ℒ(D, k, 𝐒, A), each polynomial once; reason: the proof filters by degree and agreement, so nothing else is output; the stronger reading
--   - encoding: sets S_i ⊆ 𝔽_q → duplicate-free lists in any order (S_i is the list's set); words [n, k, A, K, r, |S_1|, …, |S_n|]; reason: input layout; every order is accepted
--   - encoding: the output list has size at most q^{4r+6} → Set.encard ℒ ≤ q^{4r+6}; reason: the output is exactly ℒ
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Theorem 5.4, p.21 (PDF 23)

import Mathlib
import Definitions.Def_MatroidSensOracle_AlgRAM
import Definitions.Def_RSCapacity_ListRecovery
import Definitions.Def_RSCapacity_InterpSpace
import Definitions.Def_RSCapacity_DecoderIO

open Polynomial

set_option autoImplicit false

namespace RSCapacity

/-- **Theorem 5.4 (Prime-field sparse list recovery).** Jeronimo, arXiv:2609.05870 (held version
of November 1, 2026, sha256 9a0069bd…), Theorem 5.4, p.21 (PDF 23). Fix ϑ ∈ (0, 1). There are
effective constants r_0, a_ϑ > 0 with the following property. Let q be prime, let
α_1, …, α_n ∈ 𝔽_q be distinct, and let S_i ⊆ 𝔽_q have total incidence M. Let A, k, K be integers
with 1 ≤ A ≤ n, 1 ≤ k ≤ K, and K ≥ 2, and suppose A/(K − 1) ≥ 1/(1 − ϑ) (48),
r_0 ≤ r < K, M ≤ a_ϑ (K − 1) r^ϑ / log⁴(er) (49), B := ⌈r³A/(K − 1)⌉ < q, r³A < q² (50). Then a
deterministic algorithm outputs every P ∈ 𝔽_q[X] with deg P < k and at least A list hits. It uses
q^{O_ϑ(r)} (51) field operations, and the output list has size at most q^{4r+6}.

**Formalization Note.**
* The algorithm is one coin-free program of the published algebraic RAM over `ZMod q`; r_0, a_ϑ,
  the constant c of q^{O_ϑ(r)} and the program are chosen after ϑ only. The program halts within
  q^{c·r} steps (every instruction counts) for every word length w with q^{c·r} < 2^w, and outputs
  exactly the valid polynomials ℒ, each once.
* Input: words `[n, k, A, K, r, |S_1|, …, |S_n|]`, field cells `[α_1, …, α_n] ++ S_1 ++ ⋯ ++ S_n`;
  each S_i is a duplicate-free list in any order. log is the natural logarithm.
* The list size is `Set.encard` of ℒ (the output is exactly ℒ). -/
theorem theorem_5_4 (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) :
    ∃ r₀ : ℕ, ∃ a : ℝ, 0 < a ∧ ∃ c : ℕ, ∃ prog : List MatroidSensOracle.AInstr,
      (∀ ins ∈ prog, ¬ ins.IsCoin) ∧
      ∀ (q : ℕ) [Fact q.Prime] (n : ℕ) (α : Fin n → ZMod q), Function.Injective α →
      ∀ S : Fin n → List (ZMod q), (∀ i, (S i).Nodup) →
      ∀ A k K r : ℕ, 1 ≤ A → A ≤ n → 1 ≤ k → k ≤ K → 2 ≤ K →
        1 / (1 - ϑ) ≤ (A : ℝ) / ((K : ℝ) - 1) → r₀ ≤ r → r < K →
        (incidence (fun i => (S i).toFinset) : ℝ) ≤
          a * ((K : ℝ) - 1) * (r : ℝ) ^ ϑ / Real.log (Real.exp 1 * r) ^ 4 →
        Bdeg (r ^ 3) A K < q → r ^ 3 * A < q ^ 2 →
        (∀ w : ℕ, q ^ (c * r) < 2 ^ w →
          ∃ st, MatroidSensOracle.aexec prog (fun _ => 0) (q ^ (c * r)) 0 0
              (MatroidSensOracle.aloadWords w (sparseInstanceWords k A K r S))
              (MatroidSensOracle.aloadFields (listInstanceFields α S)) = some st ∧
            OutputsExactly k st (listSet α k (fun i => (S i).toFinset) A)) ∧
        (listSet α k (fun i => (S i).toFinset) A).encard ≤ ((q ^ (4 * r + 6) : ℕ) : ℕ∞) := by sorry

end RSCapacity
