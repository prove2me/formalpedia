-- Prove2me | Theorems.Thm_PlugInRisk_vdvw_2_7_1
-- name    : PlugInRisk.vdvw_2_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:43.479533+00:00
-- url     : https://prove2.me/theorems/0b28ad27-40ff-4c7b-899b-c08944a080cd
-- title:
--   [50, Theorem 2.7.1]: entropy of bounded 1-Lipschitz functions on $[-1,1]$
-- statement:
--   There is an absolute constant $C>0$ such that for every $\delta>0$ there is a finite family $T$ of functions on $[-1,1]$ with
--
--   $$
--   |T|\le\exp\Bigl(\frac{C}{\delta\wedge1}\Bigr)
--   $$
--
--   such that every $1$-Lipschitz function $\varphi:[-1,1]\to\mathbb R$ with $|\varphi|\le1$ has some $\varphi'\in T$ with $\sup_{t\in[-1,1]}|\varphi(t)-\varphi'(t)|\le\delta$.
--
--   This is van der Vaart and Wellner's entropy bound for Lipschitz classes, used in step (c) of the proof of Lemma 4.7 to cover the 1-Lipschitz transformations appearing in AVaR.
--
--   Differences from the source:
--
--   - reading: cardinality exp(C/((ε/a_ε)∧1)) at accuracy ε/(6C₀a_ε) → cardinality exp(C/(δ∧1)) at accuracy δ; reason: with δ = ε/(6C₀a_ε), (ε/a_ε)∧1 = (6C₀δ)∧1, so the two bounds agree after renaming the constant
--   - encoding: functions [−1,1] → ℝ → functions ℝ → ℝ with conditions and approximation on Icc (−1) 1; reason: values outside [−1,1] play no role
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, proof of Lemma 4.7, step (c), p.23, citing [50, Theorem 2.7.1]

import Mathlib

namespace PlugInRisk

/-- **Entropy of bounded 1-Lipschitz functions on [−1, 1]** ([50] = van der Vaart and Wellner,
Theorem 2.7.1, as used in Bartl & Tangpi, arXiv:2003.10479v2, proof of Lemma 4.7, step (c),
p.23): "R(L) consists of 1-Lipschitz functions which are bounded by 1 and [50, Theorem 2.7.1]
implies that there exists a set R′_ε with cardinality at most exp(C/((ε/a_ε)∧1)) such that, for
every ϕ ∈ R(L) there is ϕ′ ∈ R′_ε with sup_{t∈[−1,1]} |ϕ(t) − ϕ′(t)| ≤ ε/(6C₀a_ε)."

There is an absolute constant `C > 0` such that for every scale `δ > 0` a finite family of at
most `exp(C/(δ ∧ 1))` functions `δ`-approximates, in the supremum norm on `[−1, 1]`, every
1-Lipschitz function on `[−1, 1]` bounded by 1.

**Formalization Note** Functions on `[−1, 1]` are functions `ℝ → ℝ` whose Lipschitz and bound
conditions and approximation are required on `Set.Icc (-1) 1` only. The paper's scale
`δ = ε/(6C₀a_ε)` gives `(ε/a_ε) ∧ 1 = (6C₀δ) ∧ 1`, so its bound `exp(C/((ε/a_ε) ∧ 1))` is
`exp(C′/(δ ∧ 1))` with a renamed constant. The approximating functions need not be Lipschitz
(an external cover, as in the quote). -/
theorem vdvw_2_7_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      ∃ T : Finset (ℝ → ℝ), (T.card : ℝ) ≤ Real.exp (C / min δ 1) ∧
        ∀ φ : ℝ → ℝ, LipschitzOnWith 1 φ (Set.Icc (-1) 1) →
          (∀ t ∈ Set.Icc (-1 : ℝ) 1, |φ t| ≤ 1) →
          ∃ φ' ∈ T, ∀ t ∈ Set.Icc (-1 : ℝ) 1, |φ t - φ' t| ≤ δ := by sorry

end PlugInRisk
