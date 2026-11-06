-- Prove2me | Theorems.Thm_SilverRateLB_sec_A_3_chain_properties
-- name    : SilverRateLB.sec_A_3_chain_properties
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:07.086425+00:00
-- url     : https://prove2.me/theorems/799f432c-e5ee-4eb4-b668-5ec0a26ea402
-- title:
--   §A.3 — $F(0)=\min F=0$, $F$ is $1$-smooth, $F(x_n)\ge D_{k+1}^2/(4(1+s_{k+1}))$
-- statement:
--   Under the hypotheses of (12) (constants $a,c$ of Lemma 2.4 with $\varepsilon,\gamma>0$, a nonnegative schedule $H$, an admissible checkpoint set $T$ with $k$ checkpoints, and local hard functions $(f_i,\tau_i)$ for the gaps), the global hard function $F$ of (11) satisfies:
--   1. $F(0)=\min F=0$;
--   2. $F$ is convex and $1$-smooth;
--   3. gradient descent on $F$ with $H$ from $e_1$ ends at
--   $$F(x_n)\ \ge\ \frac{D_{k+1}^2}{4(1+s_{k+1})},$$
--   the case $k=0$ included.
--
--   Together with $\|x_0-0\|=1$ these give $\mathscr R_n(H)\ge 2F(x_n)$ and hence Lemma 2.4.
--
--   Differences from the source:
--   - generalization: the functions and thresholds (f_i, τ_i) given by Lemma 3.2 → any pairs satisfying the conclusion of Lemma 3.2 (IsLocalHard); reason: the argument uses only that conclusion; the pairs of Lemma 3.2 satisfy it
--   - encoding: F(0) = min F = 0 → F 0 = 0 ∧ ∀ x, F 0 ≤ F x; reason: same statement
--   - generalization: F is 1-smooth → KatyushaNs.IsConvexLSmooth 1 F (convex, differentiable and 1-smooth); reason: Lean also asserts convexity, which §A.3 does not state but which holds (each Φ_i is a convex f_i composed with an affine map with D_i > 0, and H_δ is convex) and which the proof of Lemma 2.4 uses to place F in the class of (1); the source's 1-smoothness is one conjunct
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), §A.3, p. 25

import Mathlib
import Definitions.Def_SilverRateLB_aOf
import Definitions.Def_SilverRateLB_IsLocalHard
import Definitions.Def_SilverRateLB_chainObjective
import Definitions.Def_KatyushaNs_IsConvexLSmooth

namespace SilverRateLB

/-- **§A.3 (smoothness and the final function value).** Under the hypotheses of (12): the
objective `F` of (11) satisfies `F(0) = min F = 0`; `F` is convex and `1`-smooth; and GD on `F`
with `H` from `e_1` ends at `F(x_n) ≥ D²_{k+1}/(4(1 + s_{k+1}))`, the case `k = 0` included.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §A.3, p. 25: "For the objective F in (11), nonnegativity and (8) give F(0) = min F = 0,
since every ℓi ≥ 0." "Each coordinate appears at most twice in the bracketed sum, so F is
1-smooth." "F(xn) ≥ ½[δ(Dk+1 − δsk+1/2) − δ²/2] = D²k+1/(4(1+sk+1)). The same calculation
includes k = 0, with t0 = ℓ1 = 0 and D1 = 1."

**Formalization Note** As for (12), the local data are any pair satisfying Lemma 3.2. "`1`-smooth"
is `KatyushaNs.IsConvexLSmooth 1 F` (convex, differentiable, `1`-Lipschitz gradient). `k = 0` is
`T = ∅`, where `F` is the one-dimensional Huber term. -/
theorem sec_A_3_chain_properties (ε γ : ℝ) (hε : 0 < ε) (hγ : 0 < γ) (H : List ℝ) (hH : ∀ h ∈ H, 0 ≤ h)
    (T : Finset ℕ) (hT : IsAdmissible H T) (f : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ) (τ : ℕ → ℝ)
    (hf : ∀ i ∈ Finset.Icc 1 T.card,
      IsLocalHard (aOf ε γ) (cOf ε γ) (gapList H T i) (ckptStep H T i) (f i) (τ i)) :
    (chainObjective (aOf ε γ) (cOf ε γ) H T f τ 0 = 0 ∧
      ∀ x, chainObjective (aOf ε γ) (cOf ε γ) H T f τ 0 ≤
        chainObjective (aOf ε γ) (cOf ε γ) H T f τ x) ∧
    KatyushaNs.IsConvexLSmooth 1 (chainObjective (aOf ε γ) (cOf ε γ) H T f τ) ∧
    chainD (aOf ε γ) (cOf ε γ) H T (T.card + 1) ^ 2 / (4 * (1 + gapMass H T (T.card + 1))) ≤
      chainObjective (aOf ε γ) (cOf ε γ) H T f τ
        (gdRun (chainObjective (aOf ε γ) (cOf ε γ) H T f τ) H (EuclideanSpace.single 0 1)) := by sorry

end SilverRateLB
