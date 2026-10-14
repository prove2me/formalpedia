-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_noisyQuantumPAC_sample_lower_bound
-- name    : QAlgorithms.Arunachalam.noisyQuantumPAC_sample_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:56:43.879225+00:00
-- url     : https://prove2.me/theorems/ca70eebb-dd14-4731-ae2d-4c9023d03b46
-- title:
--   Quantum PAC lower bound under random classification noise
-- statement:
--   Let $C\subseteq\{c:\{0,1\}^n\to\{0,1\}\}$ be a concept class with $\mathrm{VC\text{-}dim}(C)=d+1$ and let $\eta\in(0,1/2)$ be a noise rate. A quantum $(\varepsilon,\delta)$-PAC learner with noise rate $\eta$ using $T$ examples is a POVM $\{M_h\}$ on $T$ copies of the $\eta$-noisy example state
--
--   $$
--   \sum_{x\in\{0,1\}^n}\sqrt{(1-\eta)D(x)}\,|x,c(x)\rangle+\sqrt{\eta D(x)}\,|x,1-c(x)\rangle
--   $$
--
--   that, for every $c\in C$ and every distribution $D$, outputs $h$ with $\mathrm{err}_D(c,h)\le\varepsilon$ with probability at least $1-\delta$.
--
--   There are absolute constants $C_0>0$ and $d_0$ such that for all $n$, all such $C$ with $d\ge d_0$, all $\delta\in(0,1/2)$, $\varepsilon\in(0,1/20)$ and $\eta\in(0,1/2)$, every such learner using $T$ examples satisfies
--
--   $$
--   T\ \ge\ C_0\left(\frac{d}{(1-2\eta)^2\varepsilon}+\frac{\log(1/\delta)}{(1-2\eta)^2\varepsilon}\right).
--   $$
--
--   This extends Theorem 7.5.6 to random classification noise, matching the classical noisy bound.
--
--   **Formalization Note** $C_0$ and $d_0$ are quantified before every other object, so they are uniform in $\eta$ as well.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 181, Theorem 7.6.1. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning





/-- Arunachalam p.180–181, Theorem 7.6.1: let `C` be a concept class with `VC-dim(C) = d + 1`, for
sufficiently large `d`. Then for every `δ ∈ (0, 1/2)`, `ε ∈ (0, 1/20)` and `η ∈ (0, 1/2)`, every
`(ε, δ)`-PAC quantum learner for `C` with random classification noise rate `η` (given copies of
`∑_x √((1−η)D(x)) |x, c(x)⟩ + √(ηD(x)) |x, 1 − c(x)⟩`, outputting `h` with `err_D(c, h) ≤ ε` with
probability `≥ 1 − δ`, for every `c ∈ C` and every `D`) has sample complexity
`Ω(d/((1−2η)²ε) + log(1/δ)/((1−2η)²ε))`.

The constant `C₀` and the threshold `d₀` are absolute: uniform also in `η`. -/
theorem noisyQuantumPAC_sample_lower_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ d₀ : ℕ,
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d + 1 → d₀ ≤ d →
        ∀ δ ε η : ℝ, 0 < δ → δ < 1 / 2 → 0 < ε → ε < 1 / 20 → 0 < η → η < 1 / 2 →
          ∀ (T : ℕ) (M : (Qubits n → Bool) →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsNoisyQPACLearner η C ε δ T M →
              C₀ * ((d : ℝ) / ((1 - 2 * η) ^ 2 * ε) +
                Real.log (1 / δ) / ((1 - 2 * η) ^ 2 * ε)) ≤ (T : ℝ) := by
  sorry


end QAlgorithms.Arunachalam
