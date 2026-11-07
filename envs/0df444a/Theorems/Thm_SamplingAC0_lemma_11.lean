-- Prove2me | Theorems.Thm_SamplingAC0_lemma_11
-- name    : SamplingAC0.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:48:33.838535+00:00
-- url     : https://prove2.me/theorems/2b07306a-3ad1-43bb-8ff4-579c500c1d32
-- title:
--   Lemma 11 — average Lipschitzness spreads over the lines through a point
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $q=2^k$ with $k\ge1$, and let $h=(h_\ell)_{\ell\in L}$ be a decision forest on $s$ input bits with one tree per nonvertical line of $\mathbb F_q^2$. If $h$ has depth at most $q^{1/10}$ and is average-$q^{5/4}$-Lipschitz, then for a uniformly random point $v\in\mathbb F_q^2$,
--
--   $$\mathbb P_v\Bigl[\,h_{\{\ell\in L\mid\ell\ni v\}}\text{ is average-}q^{3/4}\text{-Lipschitz}\Bigr]\ \ge\ 1-c\,q^{-1/8},$$
--
--   where $h_{\{\ell\ni v\}}$ is the sub-forest of the trees of the $q$ lines through $v$.
--
--   The point-line incidence structure keeps the query load of each input bit evenly spread over the pencils of lines through points; this is the only property of the incidence used in the lower bound.
--
--   **Formalization Note** "For $1-cq^{-1/8}$-fraction of $v$" is read as "at least that fraction". Lipschitzness is with respect to the uniform input (empty restriction).
--
--   Differences from the source:
--   - encoding: "for 1 − cq^{−1/8}-fraction of v ∈ F_q²"; q a power of two; c-notation → the uniform point is good with probability ≥ 1 − c(2^k)^{−1/8}; q = 2^k with k ≥ 1; c before k, s and h; reason: same instances
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Lemma 11, p.8 (proof §3.3, p.12)

import Mathlib
import Definitions.Def_SamplingAC0_Forest
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_Restriction
import Definitions.Def_SamplingAC0_AvgLipschitz
import Definitions.Def_SamplingAC0_lineDNF
set_option autoImplicit false

namespace SamplingAC0

/-- **Lemma 11 (Lipschitzness spreads over the lines through a point).** Riazanov–Viola, *Sampling
Tools and the Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Lemma 11, p.8 (proof
p.12): "Suppose h: {0, 1}^s → {0, 1}^L is a depth-q^{1/10} average-q^{5/4}-Lipschitz decision
forest. Then for 1 − cq^{−1/8}-fraction of v ∈ F_q² the decision forest h_{{ℓ∈L | ℓ∋v}} is
average-q^{3/4}-Lipschitz."

`h` has one tree per nonvertical line of `F_q²`, `q = 2^k`; `h_{{ℓ ∋ v}}` keeps the trees of the
lines through `v`.

**Formalization Note.** "for 1 − cq^{−1/8}-fraction of v" is read as: the uniformly random point
`v` is good with probability at least `1 − cq^{−1/8}`. The constant `c` comes before `k`, `s`
and `h`. -/
theorem lemma_11 : ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (s : ℕ) (h : Forest s (Line k)),
    h.DepthLE (((2 : ℝ) ^ k) ^ ((1 : ℝ) / 10)) →
    AvgLipschitz h (Restriction.empty s) (((2 : ℝ) ^ k) ^ ((5 : ℝ) / 4)) →
    pr (PMF.uniformOfFintype (F k × F k))
        {v | AvgLipschitz (fun ℓ : {ℓ : Line k // onLine ℓ v} => h ℓ.1) (Restriction.empty s)
          (((2 : ℝ) ^ k) ^ ((3 : ℝ) / 4))}
      ≥ 1 - c * ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 8) := by sorry

end SamplingAC0
