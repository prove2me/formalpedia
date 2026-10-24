-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_ldc_two_query_lower_bound
-- name    : QAlgorithms.DeWolf.ldc_two_query_lower_bound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:44:09.562044+00:00
-- url     : https://prove2.me/theorems/1c444933-1989-4975-8678-42b03a0a1c3a
-- title:
--   2-query locally decodable codes have exponential length
-- statement:
--   This is the exponential lower bound on the length of 2-query locally decodable codes.
--
--   A map $C : \{0,1\}^n \to \{0,1\}^N$ is a $(2,\delta,\varepsilon)$-locally decodable code if for every $i \in [n]$ a classical randomized algorithm making at most $2$ queries to an $N$-bit string $y$ outputs $x_i$ with probability at least $\frac12 + \varepsilon$, for every $x \in \{0,1\}^n$ and every $y$ within Hamming distance $\delta N$ of $C(x)$.
--
--   There are constants $c > 0$ and $n_0 \in \mathbb N$ such that for all $n \ge n_0$, all $N$, all $\delta > 0$, $\varepsilon > 0$, and every $(2,\delta,\varepsilon)$-locally decodable code $C : \{0,1\}^n \to \{0,1\}^N$,
--
--   $$
--   N \ge 2^{c\,\delta^2 \varepsilon^4 n}.
--   $$
--
--   Hence the Hadamard code, of length $2^n$, is essentially optimal among 2-query LDCs.
--
--   **Formalization Note** The asymptotic $2^{\Omega(\delta^2\varepsilon^4 n)}$ is read with absolute constants $c$ and $n_0$, quantified before $N, \delta, \varepsilon$ and $C$. The threshold $n_0$ is needed: the identity code with $n = N = 1$ is a $(2, \delta, 1/2)$-LDC for every $\delta < 1$, while $1 \ge 2^{c\delta^2\varepsilon^4}$ fails for every $c > 0$.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 144, §15.3, Theorem 5. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Information
set_option autoImplicit false

namespace QAlgorithms.DeWolf



/-- de Wolf p.144, Theorem 5. If `C : {0,1}^n → {0,1}^N` is a `(2, δ, ε)`-locally decodable code,
then `N ≥ 2^{Ω(δ² ε⁴ n)}`: there are constants `c > 0` and `n₀`, uniform over `N, δ, ε, C`, such
that every `(2, δ, ε)`-LDC with `δ, ε > 0` and `n ≥ n₀` has `N ≥ 2^{c δ² ε⁴ n}`. -/
theorem ldc_two_query_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ (n N : ℕ) (δ ε : ℝ) (C : (Fin n → Bool) → (Fin N → Bool)),
        n₀ ≤ n → 0 < δ → 0 < ε → IsLDC 2 δ ε C →
        (2 : ℝ) ^ (c * δ ^ 2 * ε ^ 4 * (n : ℝ)) ≤ (N : ℝ) := by
  sorry

end QAlgorithms.DeWolf
