-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_quantumAgnostic_sample_lower_bound_info
-- name    : QAlgorithms.Arunachalam.quantumAgnostic_sample_lower_bound_info
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:54.006227+00:00
-- url     : https://prove2.me/theorems/7748b0c2-7f58-47b9-8d0b-4fb9c40991ab
-- title:
--   Quantum agnostic sample complexity lower bound (information-theoretic)
-- statement:
--   Let $C\subseteq\{c:\{0,1\}^n\to\{0,1\}\}$ be a concept class with $\mathrm{VC\text{-}dim}(C)=d\ge1$. For a distribution $D$ on $\{0,1\}^n\times\{0,1\}$ write $\mathrm{err}_D(h)=\Pr_{(x,b)\sim D}[h(x)\ne b]$ and $\mathrm{opt}_D(C)=\min_{c\in C}\mathrm{err}_D(c)$. A quantum $(\varepsilon,\delta)$-agnostic learner using $T$ examples is a POVM $\{M_h\}_{h\in C}$ on $T$ copies of $|\psi_D\rangle=\sum_{(x,b)}\sqrt{D(x,b)}\,|x,b\rangle$ that, for every $D$, outputs $h\in C$ with $\mathrm{err}_D(h)\le\mathrm{opt}_D(C)+\varepsilon$ with probability at least $1-\delta$.
--
--   For every $\delta_0\in(0,1/2)$ there is a constant $C_0>0$ such that for all $n$, all such $C$, all $\delta\in(0,\delta_0]$ and $\varepsilon\in(0,1/4)$, every quantum $(\varepsilon,\delta)$-agnostic learner for $C$ using $T$ examples satisfies
--
--   $$
--   T\ \ge\ C_0\left(\frac{d}{\varepsilon^2\log(d/\varepsilon)}+\frac{\log(1/\delta)}{\varepsilon^2}\right),
--   $$
--
--   with logarithms to base 2.
--
--   This is the agnostic analogue of Theorem 7.4.6, again tight up to the $\log(d/\varepsilon)$ factor.
--
--   **Formalization Note** The constant may depend on an upper bound $\delta_0<1/2$ for $\delta$, and $d\ge1$ is assumed: for $d=0$ the class has a single concept, which is output with no samples.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 169, Theorem 7.4.7. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning


/-- Arunachalam p.169–170, Theorem 7.4.7: let `C` be a concept class with `VC-dim(C) = d`. Then
for every `δ ∈ (0, 1/2)` and `ε ∈ (0, 1/4)`, every `(ε, δ)`-agnostic quantum learner for `C` has
sample complexity `Ω(d/(ε² log(d/ε)) + log(1/δ)/ε²)`.

Recorded corrections (trap 30), as for Theorem 7.4.4: the constant may depend on an upper bound
`δ₀ < 1/2` on `δ`, and `d ≥ 1` (at `d = 0` the class has a single concept, which is output with no
samples). The constant is uniform over `n`, `C`, `d`, `δ ∈ (0, δ₀]` and `ε`. -/
theorem quantumAgnostic_sample_lower_bound_info (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀' : δ₀ < 1 / 2) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d → 1 ≤ d →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (M : {c // c ∈ C} →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQAgnosticLearner C ε δ T M →
              C₀ * ((d : ℝ) / (ε ^ 2 * Real.logb 2 ((d : ℝ) / ε)) +
                  Real.logb 2 (1 / δ) / ε ^ 2) ≤ (T : ℝ) := by
  sorry





end QAlgorithms.Arunachalam
