-- Prove2me | Theorems.Thm_StrategicAlloc_RRFair_lemma_A_1
-- name    : StrategicAlloc.RRFair.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:15.598255+00:00
-- url     : https://prove2.me/theorems/6701ad6e-be89-4c3d-90ac-cdc8f7f5624c
-- title:
--   Lemma A.1 — a strict perturbation of $v_i$ that keeps a given best response a best response (fixed-profile reading)
-- statement:
--   Let $v_1,\dots,v_n$ be non-negative additive valuations, $i$ an agent and $b$ a bid profile. Let $\varepsilon$ be the smallest positive difference between the values of two goods under $v_i$, $\varepsilon=\min\{|v_i(g)-v_i(h)|: v_i(g)\neq v_i(h)\}$, or $\varepsilon=1$ if there is no positive difference. Then there is a valuation $v_i'$ such that
--
--   1. $v_i'$ induces a strict preference ranking on $M$ consistent with $v_i$: $v_i'$ is injective, and $v_i(g)<v_i(h)$ implies $v_i'(g)<v_i'(h)$;
--   2. if $b_i$ is a best response of agent $i$ to $b_{-i}$ in Round-Robin with respect to $v_i$, then it is still a best response with respect to $v_i'$;
--   3. for every $T\subseteq M$,
--   $$v_i(T)\ \le\ v_i'(T)\ \le\ v_i(T)+\varepsilon/3 .$$
--
--   The lemma reduces Theorem 3.4 for arbitrary valuations (ties and zeros allowed) to the strict case of Lemma 3.5.
--
--   **Formalization Note.** Agents are `Fin n` and goods `Fin m`, both 0-based (the paper's agent $i$ is $i-1$, good $g_j$ is $j-1$, and the paper's step $t$ is $t-1$). The result is stated for Round-Robin started at an arbitrary agent $s$ on an arbitrary set $G$ of goods (`rrFrom s G`); the page states the instance $s =$ agent 1, $G = M$. The proof of Theorem 3.3 (p. 10) applies the result in this generality, to Round-Robin$_\ell$ on $M' = M\setminus H$ with agent $\ell$ "in the role of agent 1"; by p. 6 this is only a renaming of the agents. The profile $b$ is fixed before $v_i'$ is chosen: the paper's proof builds $v_i'$ from the allocation of Round-Robin$(b)$, and the reading "one $v_i'$ for every $b$" is false (two agents, three goods valued $1,1,0$). The page's "with respect to $v_1$" in the definition of $\varepsilon$ means $v_i$, and the statement uses $v_i$. $\varepsilon$ is `goodGap (v i)` of the Setting. Agent $i$'s new valuation enters the best-response predicate as `Function.update v i w`.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 23, Lemma A.1

import Mathlib
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.RRFair

variable {n m : ℕ}

/-- Lemma A.1 (p. 23), fixed-profile reading, for Round-Robin started at agent `s` on the goods
`G`: for every agent `i` and bid profile `b` there is a strict valuation `w` consistent with
`v i`, under which a best response `b i` stays a best response, and whose bundle values exceed
those of `v i` by at most a third of the smallest positive gap between two goods' values. -/
theorem lemma_A_1 [NeZero n] (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (s : Fin n) (G : Finset (Fin m)) (i : Fin n) (b : Fin n → Fin m → ℝ)
    (hb : IsBidProfile b) :
    ∃ w : Fin m → ℝ, Function.Injective w ∧ (∀ g h, v i g < v i h → w g < w h) ∧
      (IsBestResponse (rrFrom s G) v b i →
        IsBestResponse (rrFrom s G) (Function.update v i w) b i) ∧
      ∀ T : Finset (Fin m),
        val v i T ≤ ∑ g ∈ T, w g ∧ ∑ g ∈ T, w g ≤ val v i T + goodGap (v i) / 3 := by sorry

end StrategicAlloc.RRFair
