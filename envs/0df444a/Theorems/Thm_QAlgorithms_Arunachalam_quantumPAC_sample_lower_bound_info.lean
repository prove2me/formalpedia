-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_quantumPAC_sample_lower_bound_info
-- name    : QAlgorithms.Arunachalam.quantumPAC_sample_lower_bound_info
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:57.060132+00:00
-- url     : https://prove2.me/theorems/6678b499-3311-45ba-af72-640fbad8797e
-- title:
--   Quantum PAC sample complexity lower bound (information-theoretic)
-- statement:
--   Let $C\subseteq\{c:\{0,1\}^n\to\{0,1\}\}$ be a non-trivial concept class (it has at least two concepts and is not of the form $\{c,1-c\}$) with $\mathrm{VC\text{-}dim}(C)=d+1$. A quantum $(\varepsilon,\delta)$-PAC learner using $T$ examples is a POVM $\{M_h\}$, indexed by hypotheses $h:\{0,1\}^n\to\{0,1\}$, acting on $T$ copies of the quantum example $|\psi_{c,D}\rangle=\sum_x\sqrt{D(x)}\,|x,c(x)\rangle$, such that for every $c\in C$ and every distribution $D$ on $\{0,1\}^n$ it outputs an $h$ with $\Pr_{x\sim D}[h(x)\neq c(x)]\le\varepsilon$ with probability at least $1-\delta$.
--
--   For every $\delta_0\in(0,1/2)$ there is a constant $C_0>0$ such that for all $n$, all such $C$, all $\delta\in(0,\delta_0]$ and $\varepsilon\in(0,1/4)$, every quantum $(\varepsilon,\delta)$-PAC learner for $C$ using $T$ examples satisfies
--
--   $$
--   T\ \ge\ C_0\left(\frac{d}{\varepsilon\log(d/\varepsilon)}+\frac{\log(1/\delta)}{\varepsilon}\right),
--   $$
--
--   with logarithms to base 2.
--
--   This is the information-theoretic quantum lower bound, tight up to the $\log(d/\varepsilon)$ factor; Section 7.5 later removes that factor.
--
--   **Formalization Note** The constant of the $\Omega$ is allowed to depend on an upper bound $\delta_0<1/2$ for $\delta$, and non-triviality of $C$ is assumed (it matters only at $d=0$); both are the hypotheses of Lemma 7.4.1, which the proof invokes for the $\log(1/\delta)/\varepsilon$ term. At $d=0$ the first term evaluates to $0$.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 168, Theorem 7.4.6. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning

/-- Arunachalam p.168–169, Theorem 7.4.6: let `C` be a concept class with `VC-dim(C) = d + 1`.
Then for every `δ ∈ (0, 1/2)` and `ε ∈ (0, 1/4)`, every `(ε, δ)`-PAC quantum learner for `C` has
sample complexity `Ω(d/(ε log(d/ε)) + log(1/δ)/ε)`.

Recorded corrections (trap 30), as for Theorem 7.4.3: the constant of the `Ω` may depend on an
upper bound `δ₀ < 1/2` on `δ` (the `log(1/δ)/ε` part is Lemma 7.4.1, which cannot hold uniformly
as `δ → 1/2`), and `C` is non-trivial (the hypothesis of Lemma 7.4.1; binding only at `d = 0`). The
constant is uniform over `n`, `C`, `d`, `δ ∈ (0, δ₀]` and `ε`. -/
theorem quantumPAC_sample_lower_bound_info (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀' : δ₀ < 1 / 2) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d + 1 →
        IsNontrivialClass C →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (M : (Qubits n → Bool) →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQPACLearner C ε δ T M →
              C₀ * ((d : ℝ) / (ε * Real.logb 2 ((d : ℝ) / ε)) + Real.logb 2 (1 / δ) / ε) ≤
                (T : ℝ) := by
  sorry






end QAlgorithms.Arunachalam
