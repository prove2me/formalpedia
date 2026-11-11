-- Prove2me | Theorems.Thm_QaryCVP_lemma_F_5
-- name    : QaryCVP.lemma_F_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:06.362272+00:00
-- url     : https://prove2.me/theorems/25cd9fe3-2dcb-4d96-a586-92fcca238637
-- title:
--   Lemma F.5 — the high-density certificate: $T_>(\delta)<0.559968479824129$, $S_>(\delta)<0.324999937051930$ on $[1,3/2]$
-- statement:
--   For $1\le\delta\le3/2$ let $u_\delta\in(0,1/3)$ satisfy $H(u_\delta,u_\delta,1-2u_\delta)=\delta$. Set $\rho=\delta$, $\eta=10^{-8}$, $(t_0,t_1,t_2,t_3)=(u_\delta+10^{-7}+\theta)(1,0.7,0.47,0.24)$ with $0\le\theta\le10^{-12}$. Then for every such $\delta$ and $\theta$:
--
--   1. $u_\delta$ is a root of $H(u,u,1-2u)=\delta$ in $(0,1/3)$;
--   2. the strict coordinate conditions, the equation conditions (5) and the even-modulus conditions (8) hold;
--   3. $H(t_0,t_0,1-2t_0)-\rho>1.99\cdot10^{-7}$;
--   4. with $a=4.138$, $\gamma=5/3$, the shifted-theta condition (22) holds;
--   5. with $\beta=2t_0$ and $c=\beta+2\cdot10^{-5}$, the exponents of (32) satisfy
--
--   $$T_>(\delta)<0.559968479824129<0.56,\qquad S_>(\delta)<0.324999937051930<0.325.$$
--
--   This certificate fixes the constants $0.56$ and $0.325$ of Theorem 1.1.
--
--   **Formalization Note** $u_\delta$ is the infimum of the root set; clause 1 says it is a root.
--
--   Differences from the source:
--   - reading: the following strict upper bounds, respectively: 0.559968479824129 < 0.56, 0.324999937051930 < 0.325 → T_>(δ) < 0.559968479824129 and S_>(δ) < 0.324999937051930; reason: the stronger of the two readings; the bounds below 0.56 and 0.325 follow
--   - encoding: the parameter ν = 16 of Section 3.1 → not mentioned; reason: ν enters only the list sizes, not these inequalities
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Lemma F.5, p.102; (12)–(14), p.34; (22), p.41; (32), p.46

import Mathlib
import Definitions.Def_QaryCVP_ent3

namespace QaryCVP

/-- **Lemma F.5** (the high-density certificate). Kim, Kwon, Lee, Lee, STOC 2027 submission
manuscript (sha256 9aeb2ff4…ab4), Lemma F.5, p.102; (12)–(14), p.34; (22), p.41; (32), p.46.

For `1 ≤ δ ≤ 3/2` let `u_δ ∈ (0, 1/3)` satisfy `H(u_δ, u_δ, 1 − 2u_δ) = δ`. Set `ρ = δ`, `η = 10⁻⁸`,
`(t₀, t₁, t₂, t₃) = (u_δ + 10⁻⁷ + θ)(1, 0.7, 0.47, 0.24)` with `0 ≤ θ ≤ 10⁻¹²`. Then:

1. `u_δ` is a root of `H(u, u, 1 − 2u) = δ` in `(0, 1/3)`;
2. the strict coordinate, nested-equation (5) and even-modulus (8) conditions hold;
3. the uniform entropy surplus `H(t₀, t₀, 1 − 2t₀) − ρ > 1.99 · 10⁻⁷`;
4. with `a = 4.138`, `γ = 5/3`, the shifted-theta condition (22) holds;
5. with `β = 2t₀`, `c = β + 2 · 10⁻⁵`, the time and space exponents of (32) satisfy
   `T_>(δ) < 0.559968479824129` and `S_>(δ) < 0.324999937051930`,

throughout the density interval and for every such `θ`.

**Formalization Note.** `u_δ` is `uDelta δ`, the infimum of the root set; clause 1 states that it
is a root. Clause 5 reads "the following strict upper bounds" as strict inequalities with the
displayed numbers (each of which is `< 0.56`, resp. `< 0.325`). The parameter `ν = 16` enters only
the list sizes, not these inequalities. -/
theorem lemma_F_5 : ∀ δ : ℝ, 1 ≤ δ → δ ≤ 3 / 2 → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 10 ^ 12 →
    let t : ℕ → ℝ := profT δ θ
    (0 < uDelta δ ∧ uDelta δ < 1 / 3 ∧ ent3 (uDelta δ) (uDelta δ) (1 - 2 * uDelta δ) = δ) ∧
    StrictCoordCond 3 t ∧ EqCond 3 δ (1 / 10 ^ 8) t ∧ ParityCond 3 δ (1 / 10 ^ 8) t ∧
    199 / 10 ^ 9 < hRate t 0 - δ ∧
    ThetaCond (9 / 25) (4138 / 1000) ∧
    Tgt δ θ < 559968479824129 / 10 ^ 15 ∧ Sgt δ θ < 324999937051930 / 10 ^ 15 := by sorry

end QaryCVP
