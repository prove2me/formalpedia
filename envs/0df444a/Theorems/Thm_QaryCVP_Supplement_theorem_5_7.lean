-- Prove2me | Theorems.Thm_QaryCVP_Supplement_theorem_5_7
-- name    : QaryCVP.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:15:21.187594+00:00
-- url     : https://prove2.me/theorems/5d86c2e1-f0df-4a14-8eb2-8070623e4921
-- title:
--   Theorem 5.7 — correctness of Algorithm 4: always a nonzero vector of $\Lambda$; shortest with probability $1-2^{-\Omega(n)}$ for all but a $2^{-\Omega(n^{2/3})}$ fraction of $H$
-- statement:
--   Fix $D\ge1$, rational constants $\delta_0\in(1/2,1)$, $\kappa\in(0,1)$, $\lambda,\varepsilon,\eta>0$, $c_0=1$, $c_1,\dots,c_k>0$ and integers $k,\nu\ge1$. Assume:
--
--   1. the padding conditions (39) hold for every $a>0$ with $\delta_0\le H(p_a)\le D$;
--   2. for all sufficiently large $n$ and all inputs with $\delta_0<\delta\le D$, the tuples $(\rho,t_0,\dots,t_k)$, with $t_i$ the proportions (34) and $\rho=\delta n/n_0$, lie in one fixed compact set on which $\rho>0$, $0<t_i<1/2$, $t_{i-1}/2<t_i<(1-t_{i-1})/2$, $d_0>d_1>\dots>d_k>0$ (with $d_0=\rho$, $d_i=r_i-\eta$), $h(2t_0)>d_0/2$, $h(2t_i)>d_{i-1}/2$ and $r_i>d_i/2+2t_i-t_{i-1}$ ($1\le i\le k$).
--
--   Run Algorithm 4 with an approximation $\hat p$ of the accuracy (34), valid interval enclosures, a nonzero exact search meeting Definition 3.4, and an enumeration $R$ whose membership events $\{\omega: v\in R(A,t;\omega)\}$ are measurable and which has the uniform bound of Lemma 3.2 on omitting a fixed vector at the actual completion parameters. Then:
--
--   1. for all integers $q\ge2$, $n\ge1$, $m\ge0$ with $\delta\le D$, every $H$ and every value of the randomness, the output is a nonzero vector of $\Lambda$;
--   2. there are $c_1,c_2>0$ and $N$ such that for all $n\ge N$ and all $q\ge2$, $m\ge0$ with $\delta\le D$, all but a $2^{-c_1n^{2/3}}$ fraction of $H$ satisfy
--
--   $$\Pr_\omega\big[\text{the output is a shortest nonzero vector of }\Lambda\big]\ \ge\ 1-2^{-c_2n},$$
--
--   with $H$ held fixed and $\omega$ the algorithm's random choices.
--
--   This is the correctness half of the SVP result; with the costs of Theorem 5.8 it gives Theorem 5.9.
--
--   **Formalization Note** Algorithm 4 is the model `alg4`; its subprocedures are arbitrary functions meeting their specifications. The randomness is independent over rounds and cases: a uniform matrix (whose last columns are $D$) and an independent $\omega\sim\mu$ for the call to $R$.
--
--   Differences from the source:
--   - generalization: Algorithm 4 run with the paper's procedures: R = Algorithm 1 / Algorithm 7, E^{≠0}_0 of Algorithm 2, b̂p as in E.6.1, the intervals of E.6.2 → the model alg4 run with arbitrary R, E0, b̂p and enclosures meeting their specifications: Definition 3.4 (nonzero), the accuracy of (34), width ≤ 1 enclosures, and for R measurable membership events and the uniform Lemma 3.2 omission bound at the actual completion parameters (InclusionBound); reason: base decision 4; the proof uses only these specifications, and the paper's R has the omission bound by the uniform version of Lemma 3.2 (§3.1.1, p.22, applied on p.53) under this theorem's compact-set hypothesis, so the paper's procedures are covered
--   - generalization: the random bits of R → an arbitrary probability space (Ω, µ) with measurable membership events {ω | v ∈ R(A, t; ω)}; reason: fair bits are a special case (as base Theorem 4.7)
--   - encoding: sample uniform D ∈ (Z/qZ)^{m×(n0−|I|)} → D = the last n0 − |I| columns of a uniform m × n0 sample, one fresh sample per round and case; reason: the marginal is uniform; independence across cases and rounds as on p.49
--   - encoding: the loops of lines 5 and 19–20 (unordered) → a fixed enumeration of the finite sets (Finset.toList); z over the box {−q, …, q}ⁿ, counts over 0..n0; reason: every z of (35) has ‖z‖² ≤ b ≤ q²; the order changes only which equally short vector is returned
--   - encoding: the tuples lie in a fixed compact set → ∃ K ⊆ ℝ × ℝ^{k+1} compact with the strict conditions on K and ∃ N with every tuple of an input with n ≥ N and δ0 < δ ≤ D in K; reason: literal
--   - encoding: δ = m log q / n ≤ D → the real density m log₂ q / n ≤ D (QaryCVP.density); reason: the same condition; D is a real constant
--   - encoding: a shortest nonzero vector, ‖x‖ = min_{a∈Λ∖{0}} ‖a‖ → x ∈ Λ, x ≠ 0 and ‖x‖² ≤ ‖a‖² for every nonzero a ∈ Λ; reason: squared form (base R7); the minimum exists since Λ ⊇ qZⁿ is discrete
--   - reading: all but a 2^{−Ω(f(n))} fraction / probability 1 − 2^{−Ω(f(n))}, for sufficiently large n → ∃ c > 0 and a threshold N, uniform in q and m, with fraction (resp. probability) ≥ 1 − 2^{−c f(n)} for n ≥ N; reason: p.12 definition of Ω for sufficiently large n (base R4)
--   - encoding: fraction of uniform matrices H → count of matrices with the property divided by q^{mn}, as a real number; reason: base R5; same instances
--   - encoding: probability over the algorithm's randomness → measure of the event under the product law, with its measurability a clause of the conclusion; reason: measurability makes the probability meaningful
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Theorem 5.7, pp.52–53 (PDF 53–54); Algorithm 4, p.48; §5.1, pp.49–50; (39), p.51; Lemma 3.2 and §3.1.1, pp.20–22

import Mathlib
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_matAvg
import Definitions.Def_QaryCVP_ent3
import Definitions.Def_QaryCVP_Supplement_svpBasics
import Definitions.Def_QaryCVP_Supplement_thetaDist
import Definitions.Def_QaryCVP_Supplement_svpExponents
import Definitions.Def_QaryCVP_Supplement_alg4

open MeasureTheory ProbabilityTheory Filter Topology

namespace QaryCVP.Supplement

/-- **Theorem 5.7** (correctness of Algorithm 4). Kim, Kwon, Lee, Lee, *Fast Provable Algorithms
for Approximate CVP and Exact SVP on Random q-ary Lattices*, STOC 2027 submission manuscript
(sha256 9aeb2ff4…ab4), Theorem 5.7, pp.52–53; Algorithm 4, p.48; §5.1, pp.49–50; (39), p.51.

Fix `D ≥ 1` and the constants `P` (`δ₀ ∈ (1/2, 1)`, `κ ∈ (0, 1)`, `λ, ε, η > 0`, `c₀ = 1`,
`c₁, …, c_k > 0`, `k, ν ≥ 1`). Assume (39) for every `a > 0` with `δ₀ ≤ H(p_a) ≤ D`, and that for all
sufficiently large `n` and all inputs with `δ₀ < δ ≤ D` the tuples `(ρ, t₀, …, t_k)`, `ρ = δn/n₀`,
lie in one fixed compact set on which `ρ > 0`, `0 < tᵢ < 1/2`, `tᵢ₋₁/2 < tᵢ < (1 − tᵢ₋₁)/2`,
`d₀ > ⋯ > d_k > 0`, `h(2t₀) > d₀/2`, `h(2tᵢ) > dᵢ₋₁/2`, `rᵢ > dᵢ/2 + 2tᵢ − tᵢ₋₁`. Run Algorithm 4
(the model `alg4`) with an accurate `b̂p`, valid enclosures, a nonzero exact search meeting its
specification, and the enumeration `R` with the uniform fixed-vector bound of Lemma 3.2 at the
actual parameters. Then:

1. for all integers `q ≥ 2`, `n ≥ 1`, `m ≥ 0` with `δ ≤ D`, every matrix and every value of the
   randomness, the output is a nonzero vector of `Λ`;
2. for sufficiently large `n`, all `q ≥ 2`, `m` with `δ ≤ D`, for all but a `2^{−Ω(n^{2/3})}` fraction
   of `H`, with `H` fixed, the output is a shortest nonzero vector of `Λ` with probability at least
   `1 − 2^{−Ω(n)}` over the algorithm's randomness.

**Formalization Note.** Decision 4 of the base mission: the subprocedures (`R`, `E^{≠0}_0`, `b̂p`, the
interval enclosures) are arbitrary functions meeting their specifications. `R` is assumed to satisfy
the uniform omission bound of Lemma 3.2 at the actual completion parameters (§3.1.1, which the
compact-set hypothesis makes applicable), with measurable membership events `{ω | v ∈ R(A, t; ω)}`. `2^{−Ω(·)}` is
`∃ c > 0, N`, uniform in `q, m` (R4); fractions count matrices (R5); `δ ≤ D` is the real density.
The compact set lives in `ℝ × ℝ^{k+1}`. -/
theorem theorem_5_7 (D : ℝ) (hD : 1 ≤ D) (P : Params) (hP : P.Admissible)
    (h39 : ∀ a : ℝ, 0 < a → (P.δ0 : ℝ) ≤ entZ (pa a) → entZ (pa a) ≤ D →
      Padding39 P.κ P.lam P.ε a)
    (bp : ℕ → ℕ → ℕ → ℚ) (hbp : BpAccurate bp) (encl : Encl) (hencl : EnclValid P encl)
    (hK : ∃ K : Set (ℝ × (Fin (P.k + 1) → ℝ)), IsCompact K ∧ (∀ x ∈ K, StrictTuple P.k P.η x) ∧
      ∃ N : ℕ, ∀ n m q : ℕ, N ≤ n → 2 ≤ q → (P.δ0 : ℝ) < density q m n → density q m n ≤ D →
        (density q m n * n / (n0Of P.κ n : ℝ), fun i : Fin (P.k + 1) => (propT P bp n m q i : ℝ))
          ∈ K)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : EnumProc Ω) (E0 : SearchProc) (hE0 : NonzeroSearchSpec E0)
    (hRmeas : ∀ (t : ℕ → ℚ) (m n0 q : ℕ) (A : Matrix (Fin m) (Fin n0) (ZMod q))
      (b : Fin m → ZMod q) (v : Fin n0 → ℤ), MeasurableSet {ω | v ∈ R t A b ω})
    (hRincl : InclusionBound P bp D μ R) :
    (∀ n m q : ℕ, 1 ≤ n → 2 ≤ q → density q m n ≤ D →
      ∀ (H : Matrix (Fin m) (Fin n) (ZMod q)) (ω : Alg4Coins P.κ n m q Ω),
        alg4 P bp encl R E0 H ω ∈ qaryLattice H ∧ alg4 P bp encl R E0 H ω ≠ 0) ∧
    (∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ N : ℕ, ∀ n m q : ℕ, N ≤ n → 2 ≤ q →
      density q m n ≤ D →
      1 - (2 : ℝ) ^ (-c₁ * (n : ℝ) ^ ((2 : ℝ) / 3)) ≤
        matFrac q m n (fun H =>
          let E : Set (Alg4Coins P.κ n m q Ω) :=
            {ω | IsShortestNonzero H (alg4 P bp encl R E0 H ω)}
          MeasurableSet E ∧ 1 - (2 : ℝ) ^ (-c₂ * n) ≤ (alg4Measure P.κ n m q μ E).toReal)) := by sorry

end QaryCVP.Supplement
