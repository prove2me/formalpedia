-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_quantumAgnostic_sample_lower_bound_optimal
-- name    : QAlgorithms.Arunachalam.quantumAgnostic_sample_lower_bound_optimal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:56:57.205122+00:00
-- url     : https://prove2.me/theorems/a8c5a962-7679-4f19-8c14-28be40bbdbe6
-- title:
--   Optimal quantum agnostic sample complexity lower bound
-- statement:
--   Let $C\subseteq\{c:\{0,1\}^n\to\{0,1\}\}$ be a concept class with $\mathrm{VC\text{-}dim}(C)=d$. A quantum $(\varepsilon,\delta)$-agnostic learner using $T$ examples is a POVM $\{M_h\}_{h\in C}$ on $T$ copies of $\sum_{(x,b)}\sqrt{D(x,b)}\,|x,b\rangle$ that, for every distribution $D$ on $\{0,1\}^{n}\times\{0,1\}$, outputs $h\in C$ with $\mathrm{err}_D(h)\le\mathrm{opt}_D(C)+\varepsilon$ with probability at least $1-\delta$, where $\mathrm{err}_D(h)=\Pr_{(x,b)\sim D}[h(x)\neq b]$ and $\mathrm{opt}_D(C)=\min_{c\in C}\mathrm{err}_D(c)$.
--
--   There are absolute constants $C_0>0$ and $d_0$ such that for all $n$, all such $C$ with $d\ge d_0$, all $\delta\in(0,1/2)$ and $\varepsilon\in(0,1/10)$, every quantum $(\varepsilon,\delta)$-agnostic learner for $C$ using $T$ examples satisfies
--
--   $$
--   T\ \ge\ C_0\left(\frac{d}{\varepsilon^2}+\frac{\log(1/\delta)}{\varepsilon^2}\right).
--   $$
--
--   This matches the classical agnostic sample complexity up to constants.
--
--   **Formalization Note** $C_0$ and $d_0$ are quantified before every other object. The source's proof is internally inconsistent in its parameter $\alpha$ ($20\varepsilon$ in the text, $10\varepsilon$ in Lemma 7.5.9); the theorem, an $\Omega$-statement, is stated as written.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 178, Theorem 7.5.8. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning



/-- Arunachalam p.178–180, Theorem 7.5.8: let `C` be a concept class with `VC-dim(C) = d`, for
sufficiently large `d`. Then for every `δ ∈ (0, 1/2)` and `ε ∈ (0, 1/10)`, every `(ε, δ)`-agnostic
quantum learner for `C` has sample complexity `Ω(d/ε² + (1/ε²) log(1/δ))`.

The constant `C₀` and the threshold `d₀` are absolute (before every other object). The proof's
parameter choice is inconsistent (the text picks `α = 20ε`, Lemma 7.5.9 computes with `α = 10ε`);
the theorem is stated as written. -/
theorem quantumAgnostic_sample_lower_bound_optimal :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ d₀ : ℕ,
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d → d₀ ≤ d →
        ∀ δ ε : ℝ, 0 < δ → δ < 1 / 2 → 0 < ε → ε < 1 / 10 →
          ∀ (T : ℕ) (M : {c // c ∈ C} →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQAgnosticLearner C ε δ T M →
              C₀ * ((d : ℝ) / ε ^ 2 + Real.log (1 / δ) / ε ^ 2) ≤ (T : ℝ) := by
  sorry




end QAlgorithms.Arunachalam
