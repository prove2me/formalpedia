-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_quantumPAC_sample_lower_bound_optimal
-- name    : QAlgorithms.Arunachalam.quantumPAC_sample_lower_bound_optimal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:56:25.153499+00:00
-- url     : https://prove2.me/theorems/016b567b-6268-43a0-aa4d-6632e451d76e
-- title:
--   Optimal quantum PAC sample complexity lower bound
-- statement:
--   Let $C\subseteq\{c:\{0,1\}^n\to\{0,1\}\}$ be a concept class with $\mathrm{VC\text{-}dim}(C)=d+1$. A quantum $(\varepsilon,\delta)$-PAC learner using $T$ examples is a POVM $\{M_h\}$, indexed by hypotheses $h:\{0,1\}^n\to\{0,1\}$, acting on $T$ copies of the quantum example $|\psi_{c,D}\rangle=\sum_x\sqrt{D(x)}\,|x,c(x)\rangle$, such that for every $c\in C$ and every distribution $D$ on $\{0,1\}^n$ it outputs an $h$ with $\Pr_{x\sim D}[h(x)\neq c(x)]\le\varepsilon$ with probability at least $1-\delta$.
--
--   There are absolute constants $C_0>0$ and $d_0$ such that for all $n$, all such $C$ with $d\ge d_0$, all $\delta\in(0,1/2)$ and $\varepsilon\in(0,1/20)$, every quantum $(\varepsilon,\delta)$-PAC learner for $C$ using $T$ examples satisfies
--
--   $$
--   T\ \ge\ C_0\left(\frac{d}{\varepsilon}+\frac{\log(1/\delta)}{\varepsilon}\right).
--   $$
--
--   Together with the classical upper bound, this shows that quantum examples do not reduce the sample complexity of PAC learning by more than a constant factor.
--
--   **Formalization Note** The constant of the $\Omega$ and the threshold for "sufficiently large $d$" are quantified before every other object, so they are uniform in $n$, $C$, $\delta$, $\varepsilon$ and the learner. The logarithm is natural; its base only changes the constant.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 175, Theorem 7.5.6. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning

/-- Arunachalam p.175–177, Theorem 7.5.6: let `C` be a concept class with `VC-dim(C) = d + 1`, for
sufficiently large `d`. Then for every `δ ∈ (0, 1/2)` and `ε ∈ (0, 1/20)`, every `(ε, δ)`-PAC
quantum learner for `C` has sample complexity `Ω(d/ε + (1/ε) log(1/δ))`.

The constant `C₀` of the `Ω` and the threshold `d₀` of "sufficiently large `d`" are absolute:
they come before `n`, `C`, `d`, `δ`, `ε` and the learner. -/
theorem quantumPAC_sample_lower_bound_optimal :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ d₀ : ℕ,
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d + 1 → d₀ ≤ d →
        ∀ δ ε : ℝ, 0 < δ → δ < 1 / 2 → 0 < ε → ε < 1 / 20 →
          ∀ (T : ℕ) (M : (Qubits n → Bool) →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQPACLearner C ε δ T M →
              C₀ * ((d : ℝ) / ε + Real.log (1 / δ) / ε) ≤ (T : ℝ) := by
  sorry






end QAlgorithms.Arunachalam
