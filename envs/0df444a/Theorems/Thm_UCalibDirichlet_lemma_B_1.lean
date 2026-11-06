-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_B_1
-- name    : UCalibDirichlet.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:54.017112+00:00
-- url     : https://prove2.me/theorems/c99f4f13-83f2-4843-82e8-ec937e0c59ea
-- title:
--   Lemma B.1 — chord gap bounded by the Bernstein error
-- statement:
--   Let $T\ge2$, $\mathcal G_T=\{0,1/T,\dots,1\}$ and $(B_Tf)(x)=\mathbb E_{S\sim\mathrm{Bin}(T,x)}[f(S/T)]$. Let $\phi:[0,1]\to\mathbb R$ be concave with $\phi(0)=\phi(1)=0$ and
--   $$\gamma:=\min_{x\in\mathcal G_T\setminus\{0,1\}}\big\{\phi(x)-(B_T\phi)(x)\big\}>0.$$
--   Then for every function $f:[0,1]\to\mathbb R$ and every $q\in[0,1]$,
--   $$qf(1)+(1-q)f(0)-f(q)\le\Big(1+\frac{\phi(q)}{\gamma}\Big)\sup_{x\in[0,1]}\big\{(B_Tf)(x)-f(x)\big\}.$$
--
--   The concave regularizer $\phi$ converts a uniform Bernstein error into a bound on the chord gap of an arbitrary (not necessarily convex) function; with $\phi$ the binary entropy (Lemma B.2) it bounds $V_F(T)$ in Lemma 2.3.
--
--   Differences from the source:
--   - encoding: γ := min over G_T ∖ {0,1} of ϕ(x) − (B_T ϕ)(x) → γ attained at some k/T with 1 ≤ k < T and a lower bound at all of them; reason: definition of the minimum over the finite interior grid
--   - encoding: (1 + ϕ(q)/γ) · sup_{x∈[0,1]} {(B_T f)(x) − f(x)} with f arbitrary → for every real ε bounding (B_T f)(x) − f(x) on [0,1]: chord gap ≤ (1 + ϕ(q)/γ)·ε; reason: equivalent (1 + ϕ(q)/γ ≥ 0 and the supremum is the least such ε); avoids the default value of a real supremum of an unbounded family
--   - encoding: ϕ, f : [0,1] → ℝ → ϕ, f : ℝ → ℝ, ϕ concave on [0,1]; reason: only values on [0,1] enter
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma B.1, displays (43)–(44), p.28

import Mathlib
import Definitions.Def_UCalibDirichlet_bern

namespace UCalibDirichlet

/-- **Lemma B.1 (chord gap from the Bernstein error).** Frongillo, Luo, Mehta & Schneider
(manuscript, STOC 2027 submission), Lemma B.1, displays (43)–(44), p.28: "Let `T ≥ 2` be an
integer, let `G_T := {0, 1/T, 2/T, …, 1}`, and let `(B_T f)(x) := E_{S∼Bin(T,x)}[f(S/T)]`. Suppose
`ϕ : [0, 1] → ℝ` is concave with `ϕ(0) = ϕ(1) = 0` and
`γ := min_{x∈G_T∖{0,1}} { ϕ(x) − (B_T ϕ)(x) } > 0`. (43)
Then for any function `f : [0, 1] → ℝ` and any `q ∈ [0, 1]`,
`qf(1) + (1 − q)f(0) − f(q) ≤ (1 + ϕ(q)/γ) sup_{x∈[0,1]} { (B_T f)(x) − f(x) }`. (44)"

**Formalization Note.** `γ` is the minimum in (43): it is attained at some interior grid point
`k/T` (`1 ≤ k ≤ T − 1`) and is a lower bound at all of them. Since `f` is arbitrary, the supremum
in (44) may be `+∞`; the conclusion is stated for every real upper bound `ε` of
`(B_T f)(x) − f(x)` on `[0, 1]`, which is equivalent to (44) (the supremum is the least such `ε`,
and `1 + ϕ(q)/γ ≥ 0`). -/
theorem lemma_B_1 (T : ℕ) (hT : 2 ≤ T) (ϕ : ℝ → ℝ) (hϕ : ConcaveOn ℝ (Set.Icc 0 1) ϕ)
    (hϕ0 : ϕ 0 = 0) (hϕ1 : ϕ 1 = 0) (γ : ℝ)
    (hγmin : ∀ k : ℕ, 1 ≤ k → k < T → γ ≤ ϕ (k / T) - bern ϕ T (k / T))
    (hγatt : ∃ k : ℕ, 1 ≤ k ∧ k < T ∧ ϕ (k / T) - bern ϕ T (k / T) = γ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (ε : ℝ)
    (hε : ∀ x ∈ Set.Icc (0 : ℝ) 1, bern f T x - f x ≤ ε) :
    q * f 1 + (1 - q) * f 0 - f q ≤ (1 + ϕ q / γ) * ε := by sorry

end UCalibDirichlet
