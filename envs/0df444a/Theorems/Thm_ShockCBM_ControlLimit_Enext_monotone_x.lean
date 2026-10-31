-- Prove2me | Theorems.Thm_ShockCBM_ControlLimit_Enext_monotone_x
-- name    : ShockCBM.ControlLimit.Enext_monotone_x
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T00:20:48.426993+00:00
-- url     : https://prove2.me/theorems/7dda2374-7e43-45cd-950b-3f51a59b4f3a
-- title:
--   Proof of Lemma 2(ii), p. 32 — $\mathbb E_s[W(s+A(s))]$ is nondecreasing in $x$ whenever $W$ is bounded, nonnegative and nondecreasing in $x$
-- statement:
--   Consider the collapsed MDP of the shock degradation model under its standing assumptions ($\alpha_0,\beta_0,a_0,b_0>0$, $0<c_p<c_u$, $0<\gamma<1$, $\xi\ge1$, $h\ge0$, and the conjugate kernel normalisable at $(a_0+x,b_0+n)$ for all $x,n\in\mathbb N$). For a state $s=(x,n,t)$ and a function $W$ on states, write
--   $$\mathbb E_s[W(s+A(s))]=\sum_{z,k\in\mathbb N}\mathbb P_s[Z=z,K=k]\,W(x+z,\,n+k,\,t+1),$$
--   where $(Z(s),K(s))$ has the joint predictive pmf at $\alpha=\alpha_0+n$, $\beta=\beta_0+t$, $a=a_0+x$, $b=b_0+n$.
--
--   Let $W$ be bounded and nonnegative ($0\le W\le B$), and non-decreasing in the degradation level: $W(x,n,t)\le W(x',n,t)$ whenever $x\le x'$. Then for all $n,t$ and $x\le x'$,
--   $$\mathbb E_{(x,n,t)}[W(s+A(s))]\le\mathbb E_{(x',n,t)}[W(s+A(s))].$$
--
--   This is the preservation step in the value-iteration proof of Lemma 2(ii): a value function that is non-decreasing in $x$ yields a continuation value that is non-decreasing in $x$, because the next state $s+A(s)$ is stochastically increasing in $x$. Raising $x$ leaves the law of the shock count $K(s)$ unchanged, and it makes the damage increment $Z(s)$ stochastically larger (Proposition 2(ii)).
--
--   **Formalization Note.** The statement is posed for an arbitrary bounded nonnegative $W$ that is non-decreasing in $x$, so it applies both to the value-iteration iterates $V^m$ and to the value function $V$.
-- source:
--   Drent, Drent, Arts, Kapodistria, Real-Time Integrated Learning and Decision Making for Cumulative Shock Degradation, Manufacturing & Service Operations Management 25(1) (2023), doi:10.1287/msom.2022.1149, accepted manuscript, proof of Lemma 2 (p. 32, step 'the expectation E_s[V^m(s+A(s))] holds this property as well', part (ii)), using Proposition 2(ii) and its proof (pp. 31-32)

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting

namespace ShockCBM.ControlLimit

theorem Enext_monotone_x (M : Model) (hM : M.Standing) (W : State → ℝ) (B : ℝ)
    (hW0 : ∀ s, 0 ≤ W s) (hWB : ∀ s, W s ≤ B)
    (hWmono : ∀ x x' n t : ℕ, x ≤ x' → W (x, n, t) ≤ W (x', n, t))
    (x x' n t : ℕ) (hxx : x ≤ x') :
    M.Enext (x, n, t) W ≤ M.Enext (x', n, t) W := by sorry

end ShockCBM.ControlLimit
