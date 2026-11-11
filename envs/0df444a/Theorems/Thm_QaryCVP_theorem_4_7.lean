-- Prove2me | Theorems.Thm_QaryCVP_theorem_4_7
-- name    : QaryCVP.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:01:04.693686+00:00
-- url     : https://prove2.me/theorems/59f106db-44d1-4ed7-ad0f-8e803cf8ccc4
-- title:
--   Theorem 4.7 — correctness of Algorithm 3: simultaneous $\gamma$-CVP for all but a $2^{-\Omega(n^{2/3})}$ fraction of $H$
-- statement:
--   Fix a constant $p\in(0,3/4]$ and bounds $0<\beta_-\le\beta_+<1$, $c_+$, $\kappa>0$ of a compact parameter set. There is a rational $C>0$, depending only on these, such that for every rational $\gamma>1$ the following holds. Run Algorithm 3 with
--
--   - parameters $\beta,c$ chosen from $n,m,q$ alone with $\beta_-\le\beta\le\beta_+$ and $\beta+\kappa\le c\le c_+$, and (11) with margin $\kappa$ on the binary correction branch: $\beta\le1/4-\kappa$, $h(\beta)\ge3/4+\kappa$;
--   - exact procedures $A$ (a closest point of $\Lambda$, Lemma 4.1) and $E_{\gamma^{-2}}$ (Definition 3.4);
--   - for $q\ge3$, a short solver $S$ which, whenever the algorithm reaches the correction branch in sufficiently large dimension, returns $\bot$ or $v\in\{-1,0,1\}^{n_0}$ with $Av=t$, $\|v\|^2\le\beta n_0$, and has average success at least $p$ for all but a $2^{-\Omega(n_0^{2/3})}$ fraction of $A$ (uniformly over the chosen parameters, at the actual rate);
--   - for $q=2$, a binary sampler $S_2$ with the guarantees of Lemma 4.2;
--   - $r=\lceil Cn\rceil$ attempts.
--
--   Then for all sufficiently large $n$ and all integers $q\ge2$, $m\ge0$ with $\delta\le3/2$, for all but a $2^{-\Omega(n^{2/3})}$ fraction of uniform $H$, holding $H$ fixed,
--
--   $$\Pr_\omega\Big[\forall y\in\mathbb Q^n:\ \text{the algorithm returns }x\in\Lambda\text{ with }\|x-y\|\le\gamma\min_{a\in\Lambda}\|a-y\|\Big]\ \ge\ 1-2^{-\Omega(n)},$$
--
--   where $\omega$ are the correction attempts' random bits, the same for every target.
--
--   **Formalization Note** Algorithm 3 is the model `alg3`. The compact subset of $\{(\beta,c):0<\beta<1,\ c>\beta\}$ is written as the box above: every compact subset lies in such a box and every such box is compact. $C$ is chosen before $\gamma$ and the procedures.
--
--   Differences from the source:
--   - generalization: Algorithm 3 run with the paper's procedures A, E_{γ^{−2}}, S, S₂ → the model alg3 run with arbitrary functions meeting their output specifications (Lemma 4.1, Definition 3.4, the hypotheses on S, Lemma 4.2 for S₂); reason: decision 4: correctness uses only the specifications; any implementation, including the paper's, is covered
--   - generalization: the solvers' internal random bits → an arbitrary probability space (Ω, μ) with measurable outcome events; reason: fair bits are a special case
--   - reading: (β, c) range over a fixed compact subset of {0 < β < 1, c > β}; (11) with uniform positive margins → β₋ ≤ β ≤ β₊, β + κ ≤ c ≤ c₊ for all (n, m, q); β ≤ 1/4 − κ and h(β) ≥ 3/4 + κ on binary correction instances; reason: equivalent descriptions of compact subsets and uniform margins
--   - reading: the feasibility checks of line 16 → an arbitrary predicate feas(n, m, q); reason: every fallback is exact; the theorem holds for any checks
--   - encoding: enumerating ker H as Bα over a basis → a fixed enumeration of the elements of ker H; reason: changes only the choice among equally close points
--   - encoding: j uniform in [ℓ′] via bounded bits → j uniform on Fin ℓ′; reason: the algorithm samples j uniformly (line 22)
--   - reading: all but a 2^{−Ω(f(n))} fraction / probability 1 − 2^{−Ω(f(n))} → ∃ c > 0 and a threshold N with fraction (resp. probability) ≥ 1 − 2^{−c f(n)} for n ≥ N; reason: p.12 definition of Ω for sufficiently large n (R4)
--   - encoding: fraction of matrices → count of matrices with the property divided by q^{mn}, as a real number; reason: R5; same instances
--   - encoding: probability of an event of the coin tape → fair-coin measure of the event, with its measurability a clause of the conclusion; reason: the event is defined from a program run; measurability makes the probability meaningful
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Theorem 4.7, p.39; Algorithm 3, p.33; (11), p.33; (15), p.34; Lemmas 4.1 and 4.2, p.35; Definition 3.4, p.24

import Mathlib
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_matAvg
import Definitions.Def_QaryCVP_ent3
import Definitions.Def_QaryCVP_corrAttempt
import Definitions.Def_QaryCVP_alg3

open MeasureTheory ProbabilityTheory

namespace QaryCVP

/-- **Theorem 4.7** (correctness of Algorithm 3). Kim, Kwon, Lee, Lee, STOC 2027 submission
manuscript (sha256 9aeb2ff4…ab4), Theorem 4.7, p.39; Algorithm 3, p.33; (11), p.33; (15), p.34;
Lemma 4.1 and Lemma 4.2, p.35; Definition 3.4, p.24.

Fix a constant `p ∈ (0, 3/4]` and bounds of a compact parameter set:
`0 < β₋ ≤ β ≤ β₊ < 1`, `c ≥ β + κ`, `c ≤ c₊`, and the margin `κ > 0` of (11). There is a rational
`C > 0`, depending only on these, such that for every rational `γ > 1` the following holds. Run
Algorithm 3 (the model `alg3`) with parameters `β, c` chosen from `n, m, q` alone in that compact set,
with (11) with margin `κ` on the binary correction branch (`β ≤ 1/4 − κ`, `h(β) ≥ 3/4 + κ`), with
exact procedures `A` (Lemma 4.1: a closest point of `Λ`) and `E_{γ^{−2}}` (Definition 3.4), with `S`
for `q ≥ 3` and `S₂` for `q = 2`, and `r = ⌈Cn⌉` attempts, where

* whenever the algorithm reaches the correction branch with `q ≥ 3` in sufficiently large
  dimension, `S` returns `⊥` or `v ∈ {−1, 0, 1}^{n₀}` with `Av = t`, `‖v‖² ≤ βn₀`, and all but a
  `2^{−Ω(n₀^{2/3})}` fraction of matrices `A` have success probability at least `p`, averaged over
  uniform `t` and its randomness (uniformly over the chosen parameters, at the actual rate);
* `S₂` is a binary sampler with the guarantees of Lemma 4.2 (output `⊥` or a `0/1` vector of weight
  at most `⌊βn₀⌋` solving `Av = t`; average success `≥ 105/128` except for a fraction (18)).

Then for all sufficiently large `n` and all integers `q ≥ 2`, `m ≥ 0` with `δ ≤ 3/2`, for all but a
`2^{−Ω(n^{2/3})}` fraction of `H`, with `H` fixed,
`Pr_ω[for every y ∈ Qⁿ the algorithm returns x ∈ Λ with ‖x − y‖ ≤ γ min_{a∈Λ}‖a − y‖] ≥ 1 − 2^{−Ω(n)}`,
`ω` being the attempts' random bits, shared by all targets.

**Formalization Note.** Decision 4: the subprocedures are arbitrary functions meeting their
specifications (a generalization: any implementation). The compact subset of
`{(β, c) : 0 < β < 1, c > β}` is written as the box `β₋ ≤ β ≤ β₊`, `β + κ ≤ c ≤ c₊`; every compact
subset lies in such a box and every such box is compact. The solvers' randomness is one probability
space `(Ω, μ)` with measurable outcome events. `2^{−Ω(·)}` is `∃ c > 0, N` (R4); fractions are counts
over the `q^{mn}` matrices (R5). `C` is chosen before `γ` and the procedures. -/
theorem theorem_4_7 (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 3 / 4) (βlo βhi chi κ : ℝ)
    (hβlo : 0 < βlo) (hβ : βlo ≤ βhi) (hβhi : βhi < 1) (hκ : 0 < κ) :
    ∃ C : ℚ, 0 < C ∧ ∀ γ : ℚ, 1 < γ →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (β c : ℕ → ℕ → ℕ → ℚ) (feas : ℕ → ℕ → ℕ → Prop)
      (Aex : ∀ {m n q : ℕ}, Matrix (Fin m) (Fin n) (ZMod q) → (Fin n → ℚ) → (Fin n → ℤ))
      (Eex : ∀ {m n q : ℕ}, Matrix (Fin m) (Fin n) (ZMod q) → (Fin n → ℚ) → ℚ →
        Option (Fin n → ℤ))
      (S S₂ : ℕ → ∀ {m n0 q : ℕ}, Matrix (Fin m) (Fin n0) (ZMod q) → (Fin m → ZMod q) → Ω →
        Option (Fin n0 → ℤ)),
      (∀ n m q : ℕ, βlo ≤ β n m q ∧ β n m q ≤ βhi ∧ (β n m q : ℝ) + κ ≤ c n m q ∧
        (c n m q : ℝ) ≤ chi) →
      (∀ n m : ℕ, ReachesCorr β feas n m 2 →
        (β n m 2 : ℝ) ≤ 1 / 4 - κ ∧ 3 / 4 + κ ≤ binEnt (β n m 2)) →
      (∀ (m n q : ℕ) (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ), 1 ≤ m → 1 ≤ n →
        2 ≤ q → IsClosest H y (Aex H y)) →
      (∀ (m n q : ℕ) (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ) (b : ℚ), 1 ≤ n →
        2 ≤ q → 0 ≤ b → IsSearchOutput (fun _ => True) H y b (Eex H y b)) →
      (∀ (n m n0 q : ℕ) (A : Matrix (Fin m) (Fin n0) (ZMod q)) (t : Fin m → ZMod q)
        (o : Option (Fin n0 → ℤ)),
        MeasurableSet {ω | S n A t ω = o} ∧ MeasurableSet {ω | S₂ n A t ω = o}) →
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∃ N₀ : ℕ,
        (∀ n m q : ℕ, N₀ ≤ n → 3 ≤ q → DensityLeThreeHalves q m n → ReachesCorr β feas n m q →
          (∀ (A : Matrix (Fin m) (Fin (n0A β n m q).toNat) (ZMod q)) (t : Fin m → ZMod q) ω v,
            S n A t ω = some v → (∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1) ∧
              A.mulVec (fun j => (v j : ZMod q)) = t ∧
              sqNormZ v ≤ β n m q * (n0A β n m q).toNat) ∧
          1 - (2 : ℝ) ^ (-c₀ * ((n0A β n m q).toNat : ℝ) ^ ((2 : ℝ) / 3)) ≤
            matFrac q m (n0A β n m q).toNat (fun A =>
              p ≤ vecAvg q m (fun t => (μ {ω | (S n A t ω).isSome}).toReal))) ∧
        (∀ n m : ℕ, N₀ ≤ n → DensityLeThreeHalves 2 m n → ReachesCorr β feas n m 2 →
          (∀ (A : Matrix (Fin m) (Fin (n0A β n m 2).toNat) (ZMod 2)) (t : Fin m → ZMod 2) ω v,
            S₂ n A t ω = some v → (∀ i, v i = 0 ∨ v i = 1) ∧
              (Finset.univ.filter (fun i => v i = 1)).card ≤
                ⌊β n m 2 * (n0A β n m 2).toNat⌋₊ ∧
              A.mulVec (fun j => (v j : ZMod 2)) = t) ∧
          1 - ((2 : ℝ) ^ ((m : ℤ) - (n0A β n m 2).toNat) +
              32 * (2 : ℝ) ^ m / (ballCard (n0A β n m 2).toNat (β n m 2) : ℝ)) ≤
            matFrac 2 m (n0A β n m 2).toNat (fun A =>
              (105 / 128 : ℝ) ≤ vecAvg 2 m (fun t => (μ {ω | (S₂ n A t ω).isSome}).toReal)))) →
      ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ N : ℕ, ∀ n m q : ℕ, N ≤ n → 2 ≤ q →
        DensityLeThreeHalves q m n →
        1 - (2 : ℝ) ^ (-c₁ * (n : ℝ) ^ ((2 : ℝ) / 3)) ≤
          matFrac q m n (fun H =>
            let E : Set (Alg3Coins C β n m q Ω) :=
              {ω | ∀ y : Fin n → ℚ, IsApproxCVP γ H y (alg3 γ C β c feas Aex Eex S S₂ H y ω)}
            MeasurableSet E ∧ 1 - (2 : ℝ) ^ (-c₂ * n) ≤ (alg3Measure C β n m q μ E).toReal) := by sorry

end QaryCVP
