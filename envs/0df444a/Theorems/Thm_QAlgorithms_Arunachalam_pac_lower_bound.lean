-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_pac_lower_bound
-- name    : QAlgorithms.Arunachalam.pac_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:43.797603+00:00
-- url     : https://prove2.me/theorems/7599a5e2-0d69-4a13-b9d0-1a2366412ac0
-- title:
--   Classical PAC sample complexity is Ω(d/ε + log(1/δ)/ε)
-- statement:
--   Let $C\subseteq\{c:\{0,1\}^n\to\{0,1\}\}$ be a concept class of VC dimension $d+1$ (the largest set shattered by $C$ has $d+1$ elements), and assume $C$ is non-trivial. A classical $(\varepsilon,\delta)$-PAC learner using $T$ examples is a randomized map from $T$ labelled examples $(x_i,c(x_i))$, $x_i\sim D$ i.i.d., to hypotheses $h:\{0,1\}^n\to\{0,1\}$ such that for every $c\in C$ and every distribution $D$ on $\{0,1\}^n$, $\Pr_{x\sim D}[h(x)\ne c(x)]\le\varepsilon$ with probability at least $1-\delta$ over the examples and the learner's randomness.
--
--   For every $\delta_0\in(0,1/2)$ there is a constant $C_0>0$ such that for all $n$, $d$, all such $C$, all $\delta\in(0,\delta_0]$, all $\varepsilon\in(0,1/4)$ and every $(\varepsilon,\delta)$-PAC learner for $C$ using $T$ examples,
--
--   $$
--   T\ \ge\ C_0\left(\frac d\varepsilon+\frac{\log(1/\delta)}{\varepsilon}\right).
--   $$
--
--   Together with the matching upper bound this pins down the classical PAC sample complexity up to constant factors.
--
--   **Formalization Note** Two corrections of the source: the constant is uniform over $\delta\le\delta_0<1/2$ (the $\log(1/\delta)/\varepsilon$ part is Lemma 7.4.1, which fails uniformly near $\delta=1/2$), and non-triviality is assumed, as Lemma 7.4.1 requires; it is automatic for $d\ge1$, and at $d=0$ the class $\{c,1-c\}$ is learned exactly from one example.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 163, Theorem 7.4.3. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_Learning
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning




/-- Arunachalam p.163–165, Theorem 7.4.3: for a concept class `C` with `VC-dim(C) = d + 1`,
every (randomized, possibly improper) classical `(ε, δ)`-PAC learner for `C` with
`ε ∈ (0, 1/4)` uses `Ω(d/ε + log(1/δ)/ε)` examples.

Corrected statement (trap 30): the constant is uniform over `δ ∈ (0, δ₀]` for each
`δ₀ < 1/2` (the `log(1/δ)/ε` part is Lemma 7.4.1, see there); and `C` is assumed non-trivial,
as Lemma 7.4.1, which the proof invokes, requires (at `d = 0` the class `{c, ¬c}` has
VC dimension 1 and is learned exactly from one example; for `d ≥ 1` non-triviality is
automatic). -/
theorem pac_lower_bound :
    ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < 1 / 2 → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d + 1 →
        IsNontrivialClass C →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (L : (Fin T → Qubits n × Bool) → PMF (Qubits n → Bool)),
            IsPACLearner C ε δ T L → C₀ * ((d : ℝ) / ε + Real.log (1 / δ) / ε) ≤ T := by
  sorry



end QAlgorithms.Arunachalam
