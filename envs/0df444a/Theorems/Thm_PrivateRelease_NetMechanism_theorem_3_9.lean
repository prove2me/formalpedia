-- Prove2me | Theorems.Thm_PrivateRelease_NetMechanism_theorem_3_9
-- name    : PrivateRelease.NetMechanism.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:40.643391+00:00
-- url     : https://prove2.me/theorems/c3e22490-7bb4-4a7a-a619-356fbe1d6724
-- title:
--   Theorem 3.9 — |N_α(C)| ≤ |X|^{O(VCDIM(C) log(1/α)/α²)}
-- statement:
--   There is an absolute constant $c_0>0$ with the following property. Let $X$ be a finite data universe, $C$ a class of predicates $\varphi:X\to\{0,1\}$ of VC-dimension $d\ge1$, and $0<\alpha\le\tfrac12$. A minimum $\alpha$-net $N_\alpha(C)$ for the counting queries of $C$ exists, and
--   $$
--   |N_\alpha(C)|\ \le\ |X|^{\,c_0\,d\log(1/\alpha)/\alpha^2}.
--   $$
--
--   It bounds the range of the Net mechanism for infinite classes, and with Corollary 3.5 yields the main utility theorem (Theorem 3.10).
--
--   **Formalization Note** The paper's $O(\cdot)$ in the exponent is an absolute constant $c_0$ quantified before the universe, the class and $\alpha$; the power is the real power. The bound is stated for every minimum net (all have the same size), together with the existence of one. The cases $d=0$ and $\alpha>\tfrac12$ are excluded. Logarithms are natural.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 10, Theorem 3.9

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_PrivateRelease_NetMechanism_Queries

namespace PrivateRelease.NetMechanism

/-- Theorem 3.9 (p. 10): there is an absolute constant `c₀ > 0` such that for every finite data
universe `X`, every class `C` of predicates of VC-dimension `d ≥ 1` and every
`0 < α ≤ 1/2`, a minimum α-net for the counting queries of `C` exists and every one has at most
`|X|^{c₀ d log(1/α)/α²}` members. -/
theorem theorem_3_9 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (X : Type) [Fintype X] (C : Set (X → Bool)) (d : ℕ) (α : ℝ),
      HighDimProb.Chaining.vcDim C = (d : ℕ∞) → 1 ≤ d → 0 < α → α ≤ 1 / 2 →
      (∃ N : Finset (Database X), IsMinNet (countingClass C) α N) ∧
        ∀ N : Finset (Database X), IsMinNet (countingClass C) α N →
          (N.card : ℝ) ≤ (Fintype.card X : ℝ) ^ (c₀ * d * Real.log (1 / α) / α ^ 2) := by sorry

end PrivateRelease.NetMechanism
