-- Prove2me | Theorems.Thm_PigeonholeDesign_Lower_lemma_4
-- name    : PigeonholeDesign.Lower.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:19:19.13178+00:00
-- url     : https://prove2.me/theorems/83b65acd-d97c-447c-bf1b-44bd8822dbd3
-- title:
--   Lemma 4 — every pigeonhole design with interval pigeonholes on [0,1] has worst-case expected discrepancy Ω(T^{1/4})
-- statement:
--   Consider sequential experiments with one continuous covariate ($p=1$, $q=0$): $T$ subjects (with $T$ even) arrive with covariates $x_1,\dots,x_T\in[0,1]$ fixed in advance, and the cost of the final split into a control group $A$ and a treated group $B$ is the discrepancy $d_{A,B}$, the minimum weight of a perfect matching between $A$ and $B$ under $|x_t-x_{t'}|$.
--
--   Let the pigeonhole design use any partition of $[0,1]$ into intervals $[l_0,l_1),[l_1,l_2),\dots,[l_{K-1},l_K]$, with $0=l_0<l_1<\dots<l_K=1$ and $K\ge1$. There are an absolute constant $c>0$ and a threshold $T_0$ such that for every even $T\ge T_0$ and every such partition, some arrival sequence $x\in[0,1]^T$ gives
--   $$\mathbb E\bigl[d_{A,B}\bigr]\;\ge\;c\,T^{1/4},$$
--   where the expectation is over the fair coins of the design. In words: every pigeonhole design suffers a worst-case expected discrepancy of order $\Omega(T^{1/4})$.
--
--   Together with Lemma 3 and Corollary 1 of the paper (an upper bound $O(T^{1/4}(\log T)^{1/2})$ for $\sqrt T$ uniform pigeonholes), this shows that the uniform pigeonhole design is optimal among pigeonhole designs up to a logarithmic factor.
--
--   **Formalization Note** The paper states the lemma for "any pigeonhole design", and Definition 3 allows any partition of the covariate space; the proof treats partitions of $[0,1]$ into $K$ intervals, and the statement is formalized for those. The constants $c$ and $T_0$ are absolute, chosen before $T$, $K$ and the breakpoints, and the hard instance is chosen after the partition. The expectation is the average over all $2^T$ coin vectors, not the discrepancy of a single run. $T^{1/4}$ is the real power.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 18, Lemma 4 (proof pp. ec15-ec16, EC.7)

import Mathlib
import Definitions.Def_PigeonholeDesign_Lower_Setting

namespace PigeonholeDesign.Lower

theorem lemma_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ (K : ℕ) (_hK : 1 ≤ K) (b : Breakpoints K), ∃ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
          c * (T : ℝ) ^ ((1 : ℝ) / 4) ≤ PigeonholeDesign.Upper.phdExp (intervalHole b) x := by sorry

end PigeonholeDesign.Lower
