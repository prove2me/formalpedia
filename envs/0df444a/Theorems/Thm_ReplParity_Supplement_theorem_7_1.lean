-- Prove2me | Theorems.Thm_ReplParity_Supplement_theorem_7_1
-- name    : ReplParity.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T15:00:30.240681+00:00
-- url     : https://prove2.me/theorems/f267e4f4-dfc0-46d6-a4e2-1c52ac44e8a3
-- title:
--   Theorem 7.1 — a finite-class learner replicable on every distribution with $O((\log(M+1)+\log(1/\rho))^2/(\varepsilon\rho^2)+\log(1/\delta)/\varepsilon)$ samples, finite-bit implementable
-- statement:
--   There is an absolute constant $C$ with the following two properties. Let $X$ be a measurable space and $H=\{h_0,\dots,h_{M-1}\}$ a nonempty finite class of measurable functions $X\to\{0,1\}$ with $M=|H|$.
--
--   1. For all real $0<\varepsilon,\delta,\rho<1$ there is a learner for $H$ that is $\rho$-replicable on every labeled distribution on $X\times\{0,1\}$ and realizably $(\varepsilon,\delta)$-PAC for $H$, with
--   $$m\le C\Big(\frac{(\log(M+1)+\log(1/\rho))^2}{\varepsilon\rho^2}+\frac{\log(1/\delta)}{\varepsilon}\Big)$$
--   samples.
--   2. If $H$ is given as a list of hypotheses that can be evaluated, the learner has a finite-bit implementation: one polynomial-time machine, the same for every $X$ and every list, which for all rationals $0<\varepsilon,\delta,\rho<1$ reads $M$, $\varepsilon$, $\rho$, the evaluation table $(h_j(x_i))$, the labels and a seed of polynomially many uniform bits, outputs a hypothesis of the list or $\bot$, uses the same number of samples and has the same two guarantees. Its running time is polynomial in $M$, $m$, the evaluation time and the encoding lengths of $\varepsilon$ and $\rho$.
--
--   So with exponential running time a parity learner ($M=2^d$) comes close to the statistical lower bound while staying replicable on every distribution.
--
--   **Formalization Note** Logarithms are natural. The class is an injective list of measurable functions; the learner reads it only through the $m\times M$ evaluation table, whose construction costs $M\cdot m$ evaluations.
--
--   Differences from the source:
--   - generalization: "there is a ρ-replicable and realizably (ε, δ)-PAC learner" (any learner, any randomness) → the learner reads the sample only through the evaluation table and the labels, and its seed is a uniform string of finitely many bits; reason: a learner of this form is a learner, so the Lean statement specializes to the source's claim; the paper's learner, with its finite-precision race, is of this form
--   - generalization: §2.2's finite-bit convention takes all parameters to be rational → the statistical clause holds for all real ε, δ, ρ in (0, 1), while the machine clause remains rational; reason: the proof's statistical construction and inequalities apply to real parameters, so the Lean clause specializes to the source's rational instances
--   - reading: "H is given as a list of hypotheses that can be evaluated … running time polynomial in M, m, the evaluation time, and the encoding lengths of ε and ρ" → one TM2 machine, polynomial-time on a fixed binary encoding of (M, ε, ρ, evaluation table, labels, seed), seed length polynomial in M + m + |ε| + |ρ|, the same machine for every X and list; the same replicability, PAC and sample bounds for this machine, for rational ε, δ, ρ; reason: building the table costs M·m evaluations, so this is the stated running time; the finite-bit model has rational parameters, and the paper's finite-precision paragraph shows the implementation keeps both guarantees (13ρ/16 < ρ)
--   - encoding: H a nonempty finite class with M = |H| → an injective list h₀, …, h_{M−1} with M ≥ 1; outputs compared as indices (an index ≥ M read as ⊥); reason: same class; by injectivity indices and hypotheses determine each other
--   - encoding: functions X → {0,1} on a domain X → measurable functions on a measurable space; labeled distributions are probability measures on X × ZMod 2; reason: err_D(h) is defined only for measurable h; standing convention
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Theorem 7.1, p.28 (PDF p.30) (= Theorem 1.5, p.3); constants (5), p.28; finite precision, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_ReplParity_Supplement_MeasureLearning
import Definitions.Def_ReplParity_Supplement_tableLearner

set_option autoImplicit false

namespace ReplParity

namespace Supplement

universe u

/-- **Theorem 7.1 (Formal version of Theorem 1.5): a replicable learner for every finite class,
replicable on every labeled distribution, with `O((log(M+1) + log(1/ρ))²/(ερ²) + log(1/δ)/ε)`
samples.** Shen, Zhong, *Replicable Parity Learning: Cubic Sample Complexity and a Geometric
Characterization*, STOC 2027 submission (manuscript sha256 40424491…), Theorem 7.1, p.28
(PDF p.30): "Let H be a nonempty finite class of functions X → {0, 1} with M = |H|. For all
0 < ε, δ, ρ < 1 there is a ρ-replicable and realizably (ε, δ)-PAC learner for H, whose
replicability holds on every labeled distribution, with
m = O((log(M + 1) + log(1/ρ))²/(ερ²) + log(1/δ)/ε) samples. If H is given as a list of hypotheses
that can be evaluated, the learner has a finite-bit implementation whose running time is polynomial
in M, m, the evaluation time, and the encoding lengths of ε and ρ."

There is an absolute constant `C` such that:
1. (statistical clause) for every measurable space `X`, every injective list `h₀, …, h_{M−1}`
   (`M ≥ 1`) of measurable functions `X → ZMod 2` and all real `0 < ε, δ, ρ < 1`, there are `m`, a
   seed length `R` and a table learner `Φ` with
   `m ≤ C((log(M+1) + log(1/ρ))²/(ερ²) + log(1/δ)/ε)` that is ρ-replicable on every labeled
   distribution and realizably `(ε, δ)`-PAC for `H = {h₀, …, h_{M−1}}`;
2. (finite-bit clause) there are a sample size `m(M, ε, δ, ρ)`, a seed length `R(M, ε, δ, ρ)`
   polynomial in `M + m + |ε| + |ρ|`, and one total function `F`, computed in polynomial time by a
   Mathlib `TM2` machine on the fixed encodings `encTIn`, `encIdx`, such that for every such `X`,
   list and rationals `0 < ε, δ, ρ < 1`, the learner that runs `F` on
   `(M, ε, ρ, (h_j(x_i)), (y_i), r)` has the same sample bound and the same two guarantees.

**Formalization Note.** `H` is the injective list (so `M = |H|`), and the learner reads it only
through the `m × M` evaluation table, which costs `M·m` evaluations to build; the machine's time is
polynomial in its input, whose length is polynomial in `M, m`, the seed length and the encoding
lengths of `ε, ρ`. The seed is `R` uniform bits in both clauses. Logarithms are natural. -/
theorem theorem_7_1 :
    ∃ C : ℝ,
      (∀ (X : Type u) [MeasurableSpace X] (M : ℕ) (h : Fin M → X → ZMod 2),
        1 ≤ M → Function.Injective h → (∀ j, Measurable (h j)) →
        ∀ ε δ ρ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → 0 < ρ → ρ < 1 →
          ∃ m R : ℕ, ∃ Φ : (Fin m → Fin M → ZMod 2) → (Fin m → ZMod 2) → (Fin R → Bool) →
              Option (Fin M),
            (m : ℝ) ≤ C * ((Real.log (M + 1) + Real.log (1 / ρ)) ^ 2 / (ε * ρ ^ 2) +
              Real.log (1 / δ) / ε) ∧
            IsReplicableM (tableLearner h Φ) ρ ∧
            IsRealizablyPACM (Set.range h) (fun S r => (tableLearner h Φ S r).map h) ε δ) ∧
      (∃ m R : ℕ → ℚ → ℚ → ℚ → ℕ, ∃ F : TInput → Option ℕ,
        Nonempty (Turing.TM2ComputableInPolyTime encTIn encIdx F) ∧
        (∃ k c : ℕ, ∀ (M : ℕ) (ε δ ρ : ℚ),
          R M ε δ ρ ≤ c * (M + m M ε δ ρ + ratSize ε + ratSize ρ) ^ k + c) ∧
        ∀ (X : Type u) [MeasurableSpace X] (M : ℕ) (h : Fin M → X → ZMod 2),
          1 ≤ M → Function.Injective h → (∀ j, Measurable (h j)) →
          ∀ ε δ ρ : ℚ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → 0 < ρ → ρ < 1 →
            ((m M ε δ ρ : ℝ) ≤ C * ((Real.log (M + 1) + Real.log (1 / (ρ : ℝ))) ^ 2 /
              ((ε : ℝ) * (ρ : ℝ) ^ 2) + Real.log (1 / (δ : ℝ)) / ε)) ∧
            IsReplicableM
              (tableLearner (m := m M ε δ ρ) (Ω := Fin (R M ε δ ρ) → Bool) h
                (runTable F M ε ρ)) (ρ : ℝ) ∧
            IsRealizablyPACM (Set.range h)
              (fun S r => (tableLearner (m := m M ε δ ρ) (Ω := Fin (R M ε δ ρ) → Bool) h
                (runTable F M ε ρ) S r).map h) (ε : ℝ) (δ : ℝ)) := by sorry

end Supplement

end ReplParity
