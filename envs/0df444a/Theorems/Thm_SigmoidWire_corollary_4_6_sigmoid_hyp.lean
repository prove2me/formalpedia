-- Prove2me | Theorems.Thm_SigmoidWire_corollary_4_6_sigmoid_hyp
-- name    : SigmoidWire.corollary_4_6_sigmoid_hyp
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:22.529189+00:00
-- url     : https://prove2.me/theorems/7607e0cc-9cb8-4b02-b0ed-ab5885747642
-- title:
--   Proof of Corollary 4.6: Sigmoid meets the hypotheses of Theorem 4.4 with $\kappa=1/4$, $c=2$
-- statement:
--   The function $\mathrm{Sigmoid}$ takes values in $[0,1]$, is non-decreasing, satisfies $|\mathrm{Sigmoid}(x)-\mathrm{Sigmoid}(y)|\le\frac14|x-y|$, and for some $c_0\ge1$ satisfies the rational-approximation condition of Theorem 4.4 with $c=2$: for all integers $k\ge1$ and reals $a\ge1$ there is a rational function of degree at most $k$ with no pole in $[-a,a]$ approximating it on $[-a,a]$ within $c_0a^{c_0}e^{-\sqrt k/c_0}$.
--
--   This instantiates Theorem 4.4 for sigmoidal circuits, and it shows the hypothesis of that theorem is satisfiable.
--
--   Differences from the source:
--   - reading: "it satisfies the condition in Theorem 4.4 with c = 2", with c₀ unnamed → ∃ c₀ ≥ 1; reason: Theorem 4.4 asks for some constant c₀ ≥ 1
--   - encoding: σ : ℝ → [0, 1] in Theorem 4.4 → the conjunct Sigmoid(x) ∈ [0, 1]; reason: in Lean σ is a real function, so its range is a separate clause
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof of Corollary 4.6, p.20

import Mathlib
import Definitions.Def_SigmoidWire_RatApproxOn

namespace SigmoidWire

/-- **Proof of Corollary 4.6: Sigmoid meets the hypotheses of Theorem 4.4 with `κ = 1/4`, `c = 2`.**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof of Corollary 4.6, p.20
(PDF p.22): "Let σ := Sigmoid, which is non-decreasing and κ-Lipschitz for κ = 1/4, and by Lemma 4.5
it satisfies the condition in Theorem 4.4 with c = 2."

**Formalization Note.** The conjuncts are: `Sigmoid` maps into `[0, 1]` (Theorem 4.4's
`σ : ℝ → [0, 1]`), is monotone, is `1/4`-Lipschitz, and satisfies `RatApproxCond Real.sigmoid 2 c₀`
(the shared definition of Theorem 4.4's condition) for some `c₀ ≥ 1`. -/
theorem corollary_4_6_sigmoid_hyp :
    (∀ x : ℝ, Real.sigmoid x ∈ Set.Icc (0 : ℝ) 1) ∧
    Monotone Real.sigmoid ∧
    (∀ x y : ℝ, |Real.sigmoid x - Real.sigmoid y| ≤ (1 / 4 : ℝ) * |x - y|) ∧
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ RatApproxCond Real.sigmoid 2 c₀ := by sorry

end SigmoidWire
