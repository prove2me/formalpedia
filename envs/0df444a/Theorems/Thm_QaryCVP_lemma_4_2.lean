-- Prove2me | Theorems.Thm_QaryCVP_lemma_4_2
-- name    : QaryCVP.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:54.023004+00:00
-- url     : https://prove2.me/theorems/b79926aa-bf3b-42b8-a99f-7e95a89c99c2
-- title:
--   Lemma 4.2 — the binary sampler $S_2$ succeeds on average with probability $\ge105/128$
-- statement:
--   Fix a rational $0<\beta<1/2$. There is a randomized program $S_2$ such that for integers $n_0\ge1$ and $1\le m\le n_0$, with $B=\{x\in\mathbb F_2^{n_0}:\mathrm{wt}(x)\le\lfloor\beta n_0\rfloor\}$:
--
--   1. on every input $(A,t)\in\mathbb F_2^{m\times n_0}\times\mathbb F_2^m$ and every execution, $S_2$ returns either $\bot$ or $x\in B$ with $Ax=t$, represented by integer coordinates in $\{0,1\}$; it uses time $(2^{n_0}/|B|)\,\mathrm{poly}(n_0,m)$, polynomial space and polynomially many random bits;
--   2. except for a fraction at most
--
--   $$2^{m-n_0}+32\cdot2^m/|B|\qquad(18)$$
--
--   of matrices $A$, its average success probability over a uniform right-hand side and independent internal randomness is at least $105/128>3/4$.
--
--   It is the short solver of the correction step for $q=2$.
--
--   Differences from the source:
--   - reading: the procedure (a specific algorithm of the paper) → there is a program of the RAM with every stated property, bundled for the same program; reason: decision 3: writing the algorithm as RAM code inside a statement is not feasible; the bundle carries every property later steps use
--   - reading: time and space in bit operations and bits, no machine named (p.13) → bit time and bit space of the published randomized log-cost rational RAM TwMSOCount.Main; reason: the paper's cost model; this machine charges bit operations at least as heavily (decision 1)
--   - reading: on every input and execution → the run halts on every coin tape and the bounds hold on every tape; reason: p.13, Theorem 1.1
--   - reading: poly(n₀, m), polynomial space, polynomially many random bits → (n₀ + m + 1)^K bounds on time factor, bit space and the number of coins read; reason: one degree K for all three, fixed before the input
--   - encoding: fraction of matrices → count of matrices with the property divided by q^{mn}, as a real number; reason: R5; same instances
--   - encoding: probability of an event of the coin tape → fair-coin measure of the event, with its measurability a clause of the conclusion; reason: the event is defined from a program run; measurability makes the probability meaningful
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Lemma 4.2 and (18), p.35

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_matAvg
import Definitions.Def_QaryCVP_encInst

open MeasureTheory TwMSOCount.Main
open scoped ENNReal

namespace QaryCVP

/-- **Lemma 4.2** (binary short-solution sampler). Kim, Kwon, Lee, Lee, STOC 2027 submission
manuscript (sha256 9aeb2ff4…ab4), Lemma 4.2 and (18), p.35.

Fix a rational `0 < β < 1/2`. There is a randomized program `S₂` and a degree `K` such that, for
integers `n₀ ≥ 1` and `1 ≤ m ≤ n₀`, with `B = {x ∈ F₂^{n₀} : wt(x) ≤ ⌊βn₀⌋}`:

1. on every input `(A, t) ∈ F₂^{m×n₀} × F₂^m` and every execution, `S₂` returns `⊥` or `x ∈ B` with
   `Ax = t`, represented by integer coordinates in `{0, 1}`; it uses bit time
   `(2^{n₀}/|B|) poly(n₀, m)`, polynomial space and polynomially many random bits;
2. except for a fraction at most `2^{m−n₀} + 32 · 2^m/|B|` (18) of matrices `A`, its average success
   probability over a uniform right-hand side and independent internal randomness is at least
   `105/128`.

**Formalization Note.** Decision 3 (existential form). `poly(n₀, m)` is `(n₀ + m + 1)^K`; the number
of random bits is the number of coins read by the run. The success events are measurable (a clause
of the conclusion). `105/128 > 3/4` is arithmetic. -/
theorem lemma_4_2 (β : ℚ) (hβ0 : 0 < β) (hβ1 : β < 1 / 2) :
    ∃ (S₂ : Program) (K : ℕ), ∀ n0 m : ℕ, 1 ≤ n0 → 1 ≤ m → m ≤ n0 →
      (∀ (A : Matrix (Fin m) (Fin n0) (ZMod 2)) (b : Fin m → ZMod 2),
        (∀ ω : ℕ → Bool, ∃ s : RunStats, runStats S₂ ω (Config.init (encShort A b)) = some s ∧
          (s.time : ℝ) ≤ (2 : ℝ) ^ n0 / (ballCard n0 β : ℝ) * ((n0 : ℝ) + m + 1) ^ K ∧
          (s.space : ℝ) ≤ ((n0 : ℝ) + m + 1) ^ K ∧
          (s.final.coins : ℝ) ≤ ((n0 : ℝ) + m + 1) ^ K ∧
          (s.final.output = [] ∨ ∃ x : Fin n0 → ℤ, s.final.output = encZVec x ∧
            (∀ i, x i = 0 ∨ x i = 1) ∧
            (Finset.univ.filter (fun i => x i = 1)).card ≤ ⌊β * n0⌋₊ ∧
            A.mulVec (fun j => (x j : ZMod 2)) = b)) ∧
        MeasurableSet (firstSucc S₂ A b)) ∧
      1 - ((2 : ℝ) ^ ((m : ℤ) - n0) + 32 * (2 : ℝ) ^ m / (ballCard n0 β : ℝ)) ≤
        matFrac 2 m n0 (fun A =>
          (105 / 128 : ℝ) ≤ vecAvg 2 m (fun b => (coinTape (firstSucc S₂ A b)).toReal)) := by sorry

end QaryCVP
