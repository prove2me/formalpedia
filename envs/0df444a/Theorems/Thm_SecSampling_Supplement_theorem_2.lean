-- Prove2me | Theorems.Thm_SecSampling_Supplement_theorem_2
-- name    : SecSampling.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:02:40.881375+00:00
-- url     : https://prove2.me/theorems/23589de6-88a5-497b-a3e4-c40dde525010
-- title:
--   Theorem 2 — one universal $ALG_t$ is optimal for ROSp, with limits $1/e$ and $\gamma$
-- statement:
--   There is one admissible threshold sequence $t$, chosen independently of the sampling probability and the instance size, such that for every $p\in[0,1)$ the success guarantee of $ALG_t$ is at least the success guarantee of every ordinal, possibly randomized ROSp algorithm.
--
--   Writing $F(p,t)$ for Eq. (1), the same sequence satisfies
--   $$
--   F(0,t)=e^{-1},\qquad \lim_{p\to1^-}F(p,t)=\gamma,
--   $$
--   where $\gamma$ is Samuels' exact constant from Lemma 22.
--
--   Thus $ALG_t$ is universally optimal across sampling probabilities, equals the classical $1/e$ guarantee without samples, and approaches the full-information secretary optimum as sampling becomes complete.
--
--   **Formalization Note** `ALG_t` is evaluated in the equivalent arrival-time formulation, while competing algorithms use the original uniform-order ordinal-history formulation. Guarantees are characterized by lower bounds and epsilon-attainment. The exact formula for $\gamma$ replaces only the source's decimal shorthand.
--
--   Differences from the source:
--   - encoding: “best possible success guarantee” → $F(p,t)$ is the epsilon-characterized guarantee of $ALG_t$, and every ordinal algorithm has some size and value instance within every positive epsilon above $F(p,t)$; reason: this expands the two infimum comparisons without a junk real `sInf` or a conditional guarantee witness
--   - encoding: original ROSp and its equivalent arrival-time formulation → competitors use the uniform-permutation model and $ALG_t$ uses product-uniform arrival times, with equal-time ties broken by index; reason: §3 proves the formulations equivalent and ties have probability zero
--   - encoding: $\gamma\approx0.58$ → the exact Samuels formula with corrected coefficient $e^c-1-c$; reason: the theorem cites Samuels' constant and Lemma 22 supplies its exact formula
-- source:
--   Correa, Cristi, Feuilloley, Oosterwijk & Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, Theorem 2, p.11 (PDF p.12), with Lemmas 2–6 and 22

import Definitions.Def_SecSampling_Supplement_ROSp

open Filter Set Topology

namespace SecSampling.Supplement

/-- **Theorem 2** (Correa et al., arXiv:2011.07869v1, p.11, PDF p.12). One admissible sequence
`t`, chosen independently of `p` and `n`, makes `ALG_t` optimal for ROSp at every
`p ∈ [0,1)`. Its guarantee is `1/e` at `p=0`, and as `p→1⁻` its guarantee tends to Samuels'
constant `γ`.

**Formalization Note.** Optimality compares Eq. (1), which Lemma 3 identifies as `ALG_t`'s
guarantee in the equivalent arrival-time formulation, with every guarantee of every base
ordinal behavioural algorithm in the original uniform-order formulation. `IsALGTGuarantee` uses
lower-bound plus epsilon-attainment clauses; the upper bound on a competitor directly produces an
instance within every positive epsilon of `ALG_t`'s value. Thus no default real infimum or
conditional existence of an infimum witness can trivialize the statement. The constant is the
exact formula `samuelsGamma c`, not the decimal approximation. Equal arrival times are broken by
index in the arrival model; that null event does not change any probability. -/
theorem theorem_2 :
    ∃ (t : ℕ → ℝ) (c : ℝ),
      IsAdmissible t ∧ IsSamuelsC c ∧
      (∀ (p : ℝ), p ∈ Ico (0 : ℝ) 1 →
        IsALGTGuarantee p t (eqOne p t) ∧
        ∀ A : SecSampling.Algorithm, SecSampling.IsAlgorithm A →
          ∀ ε : ℝ, 0 < ε →
            ∃ (n : ℕ) (v : Fin n → ℝ), Function.Injective v ∧
              rospWinProb p A v < eqOne p t + ε) ∧
      eqOne 0 t = Real.exp (-1) ∧
      Tendsto (fun p : ℝ => eqOne p t) (nhdsWithin 1 (Iio 1))
        (nhds (samuelsGamma c)) := by sorry

end SecSampling.Supplement
