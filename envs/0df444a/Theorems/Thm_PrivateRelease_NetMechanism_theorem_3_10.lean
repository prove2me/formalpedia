-- Prove2me | Theorems.Thm_PrivateRelease_NetMechanism_theorem_3_10
-- name    : PrivateRelease.NetMechanism.theorem_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:31.80981+00:00
-- url     : https://prove2.me/theorems/f45aedb2-d2ce-41be-9d36-a5f802183119
-- title:
--   Theorem 3.10 — the Net mechanism is (α, δ)-useful once α ≥ O((VCDIM(C) log|X| log(1/α) + log(1/δ))/(εα²n))
-- statement:
--   There is an absolute constant $c>0$ with the following property. Let $X$ be a finite data universe, $C$ a class of predicates $\varphi:X\to\{0,1\}$ of VC-dimension $d\ge1$, $n\ge1$ the input size, $\varepsilon>0$, $0<\delta\le1$ and $0<\alpha\le\tfrac12$. If
--   $$
--   \alpha\ \ge\ \frac{c}{\varepsilon\alpha^2 n}\Big(d\,\log|X|\,\log\frac1\alpha+\log\frac1\delta\Big),
--   $$
--   then a minimum $\tfrac\alpha2$-net $N$ for the counting queries of $C$ exists, and the Net mechanism with privacy parameter $\varepsilon$ run on any such $N$ is $(\alpha,\delta)$-useful for $C$: for every input $z\in X^n$, with probability at least $1-\delta$ its output $\hat D$ satisfies $|Q_\varphi(\hat D)-Q_\varphi(z)|\le\alpha$ for every $\varphi\in C$.
--
--   This is the paper's main utility theorem: ignoring computation, any class of counting queries of polynomial VC-dimension over a discretized universe admits a differentially private (Property 3.3) synthetic-database release whose error decays with the database size $n$.
--
--   **Formalization Note** The paper writes $\alpha\ge O(\cdot)$; the $O(\cdot)$ is an absolute constant $c$ quantified before every other binder. The paper obtains $(\alpha,\delta)$ from Corollary 3.5's $(2\alpha',\delta)$ at $\alpha'=\alpha/2$, so the mechanism runs on a minimum $\alpha/2$-net and the factor $2$ is absorbed into $c$. The hypotheses $d\ge1$, $\alpha\le\tfrac12$ (so $\log(1/\alpha)>0$) are disclosed exclusions. Privacy is Property 3.3 and is not restated. Neighbours differ in exactly one entry; logarithms are natural.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 10, Theorem 3.10 (first display)

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_PrivateRelease_NetMechanism_ExpMech

namespace PrivateRelease.NetMechanism

/-- Theorem 3.10 (p. 10): there is an absolute constant `c > 0` such that for every finite data
universe `X`, every class `C` of counting queries of VC-dimension `d ≥ 1`, every
input size `n ≥ 1`, every `ε > 0`, `0 < δ ≤ 1` and `0 < α ≤ 1/2` with
`α ≥ (c/(ε α² n)) (d log|X| log(1/α) + log(1/δ))`, a minimum `α/2`-net for `C` exists and the
Net mechanism run on any minimum `α/2`-net is `(α, δ)`-useful for `C` on inputs of size `n`. -/
theorem theorem_3_10 :
    ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [Fintype X] (C : Set (X → Bool)) (d n : ℕ) (ε α δ : ℝ),
      HighDimProb.Chaining.vcDim C = (d : ℕ∞) → 1 ≤ d → 1 ≤ n →
      0 < ε → 0 < α → α ≤ 1 / 2 → 0 < δ → δ ≤ 1 →
      c / (ε * α ^ 2 * n) *
          (d * Real.log (Fintype.card X : ℝ) * Real.log (1 / α) + Real.log (1 / δ)) ≤ α →
      (∃ N : Finset (Database X), IsMinNet (countingClass C) (α / 2) N) ∧
        ∀ N : Finset (Database X), IsMinNet (countingClass C) (α / 2) N →
          Useful (countingClass C) α δ (netMech (n := n) (countingClass C) ε N) := by sorry

end PrivateRelease.NetMechanism
