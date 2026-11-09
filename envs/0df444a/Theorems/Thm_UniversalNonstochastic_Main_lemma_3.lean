-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_lemma_3
-- name    : UniversalNonstochastic.Main.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:07:00.369494+00:00
-- url     : https://prove2.me/theorems/4be0a880-41cb-4932-9993-ca3e7327192f
-- title:
--   Lemma 3 — the universal tail is stable under computable growth
-- statement:
--   Let $\tau(t)=\mathbf m(\{n\in\mathbb N:n>t\})$ be the tail of a universal semimeasure $\mathbf m$. For every computable nondecreasing function $g:\mathbb N_0\to\mathbb N_0$ there is a constant $c_g>0$ such that
--   $$\tau(g(t))\;\ge\;c_g\,\tau(t)\qquad\text{for all }t\in\mathbb N_0 .$$
--
--   Thus the tail hardly changes even when its argument is replaced by an enormous computable function of itself, such as $2^{2^t}$. In the proof of Theorem 1 this converts the stronger lower bound $\tau(\max(\alpha,\beta))$ into $\tau(\alpha)$ when $\beta\le 2^{2^\alpha}$. No assumption $g(t)\ge t$ is made.
--
--   Differences from the source:
--   - encoding: m: a fixed universal semimeasure on ℕ, m(A) = Σ_{a∈A} m(a) → m : UniversalSemimeasure (arbitrary), mass m A = real tsum of the indicator; reason: the weights are nonnegative with partial sums ≤ 1, so the real sum is the true sum; the statement is quantified over every universal semimeasure
--   - encoding: “increasing” (in the wide sense) → Monotone g; reason: the source states (p.4) that increasing allows intervals of constancy
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/11.pdf, Lemma 3, p.6 (PDF p.6); proof p.16

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure

namespace UniversalNonstochastic.Main

/-- Lemma 3, p.6: for every computable nondecreasing `g : ℕ₀ → ℕ₀` there is `c_g > 0`
with `τ(g(t)) ≥ c_g τ(t)` for all `t ∈ ℕ₀`. -/
theorem lemma_3 (m : UniversalSemimeasure) (g : ℕ → ℕ) (hg_comp : Computable g)
    (hg_mono : Monotone g) :
    ∃ cg : ℝ, 0 < cg ∧ ∀ t : ℕ, cg * tail m (t : ℝ) ≤ tail m (g t : ℝ) := by sorry

end UniversalNonstochastic.Main
