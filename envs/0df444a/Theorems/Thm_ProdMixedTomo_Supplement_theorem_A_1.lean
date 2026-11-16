-- Prove2me | Theorems.Thm_ProdMixedTomo_Supplement_theorem_A_1
-- name    : ProdMixedTomo.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:32:42.010278+00:00
-- url     : https://prove2.me/theorems/516ccb9d-5d81-4e8b-bd2b-bd7c82cc8ffd
-- title:
--   Theorem A.1 — robust $\ell_2$ mean estimation of binary products from $\tilde O(n/\epsilon^2)$ samples, error $O(\epsilon\sqrt{\log1/\epsilon})$
-- statement:
--   There are universal constants $\epsilon_0,C>0$ and one classical program $P$ of the base measuring machine such that for every $n$, every $0<\epsilon\le\epsilon_0$, every mean vector $\mu\in[0,1]^n$, every $\epsilon$-corruption adversary $\mathrm{Adv}$ and every
--   $$
--   N\ \ge\ C\cdot X\cdot(\log(2+X))^C,\qquad X=\frac{n}{\epsilon^2},
--   $$
--   the following hold when $P$ is run on input $(n,N,\epsilon)$ and the corrupted list $\mathrm{Adv}(S_g)$, with $S_g$ a list of $N$ i.i.d. samples from the product distribution $\mathrm{Bern}(\mu)$ on $\{0,1\}^n$:
--   1. on every input of size $N$ and every run, $P$ halts within $C(N+1)^C$ steps;
--   2. with probability at least $0.99$ (over the clean samples and the program's coins) the output vector $\hat\mu\in\mathbb R^n$ satisfies
--   $$
--   \|\hat\mu-\mu\|_2\ \le\ C\,\epsilon\,\sqrt{\max\{1,\log(1/\epsilon)\}}.
--   $$
--   Its sample complexity is linear in $n$, against $n^2$ for the total-variation learner of Theorem 4.5; it is the estimation primitive behind the pure-state tomography result, Theorem 3.6.
--
--   Differences from the source:
--   - reading: "Let ϵ0 > 0 be some universal constant. There is an algorithm" → ∃ ϵ₀ > 0 chosen together with C and the program; reason: ϵ₀ is a constant fixed by the proof (as in Theorem 4.5); for ϵ ≥ 1/2 no estimator can succeed
--   - reading: Õ(n/ϵ²) → C·X·(log(2 + X))^C with X = n/ϵ²; reason: polylog of the printed argument (the stronger reading of Õ, reading R2 of the base mission)
--   - encoding: "an algorithm", "runs in time poly(N)" → an admissible classical program of the measuring real RAM halting within ⌊C·(N + 1)^C⌋ steps on every input and every run; reason: the paper names no machine (base reading R1); N + 1 because every run needs a step and N may be 0
--   - encoding: ϵ-corrupted set of samples (Definition 2.1) → an ϵ-corruption adversary applied to N i.i.d. clean samples, the failure probability summed over clean lists with their Bern(μ)^N weight; reason: the base mission's corruption model (the adversary sees the clean sample, not the coins)
--   - encoding: input of the algorithm → (n, N, ϵ, samples), the second real input cell set to 0; reason: Algorithm 3 uses ϵ and no δ
--   - encoding: unknown product distribution p ∈ P_n with mean μ → Bern(μ) with μ ∈ [0,1]ⁿ; reason: a binary product distribution is determined by its mean
--   - reading: ‖μ̂ − μ‖₂ ≲ ϵ√log 1/ϵ → ≤ C·ϵ·√max{1, log(1/ϵ)}; reason: ≲ and the log convention of p.13
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem A.1, p.51 (PDF p.53); Algorithm 3, p.53 (PDF p.55)

import Mathlib
import Definitions.Def_ProdMixedTomo_Rates
import Definitions.Def_ProdMixedTomo_BinaryProduct
import Definitions.Def_ProdMixedTomo_Machine
import Definitions.Def_ProdMixedTomo_Corruption
import Definitions.Def_ProdMixedTomo_Supplement_gHalf

namespace ProdMixedTomo.Supplement

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem A.1, p.51 (PDF p.53). Let `ϵ₀ > 0` be some universal constant. There is an
algorithm which, given an `ϵ`-corrupted set of samples from an unknown product distribution
`p ∈ P_n` with mean `μ`, for `ϵ ≤ ϵ₀`, of size `N ≥ N₀ = Õ(n/ϵ²)`, outputs with probability
`0.99` a mean vector `μ̂` with `‖μ̂ − μ‖₂ ≲ ϵ√log 1/ϵ`, and runs in time `poly(N)`.

**Formalization Note.** `ϵ₀` is existential, chosen with `C` and the program (as in the base
`theorem_4_5`). The algorithm is a classical program of the base machine with input
`(n, N, ϵ, 0, samples)` (the second real parameter is unused, `0`); the adversary sees the clean
samples `S ∼ Bern(μ)^N`, not the coins. On every input of size `N` and every run it halts within
`⌊C·(N + 1)^C⌋` steps; the failure probability of `{not halted} ∪ {‖μ̂ − μ‖₂ > C·gHalf(ϵ)}` is at most
`1/100`, with `μ̂` the raw output vector `outVec` and `gHalf(ϵ) = ϵ·√(max{1, log(1/ϵ)})`. -/
theorem theorem_A_1 :
    ∃ ϵ₀ C : ℝ, 0 < ϵ₀ ∧ 0 < C ∧ ∃ P : Program, Admissible P ∧ IsClassical P ∧
    ∀ (n N : ℕ) (ϵ : ℝ) (ν : Fin n → ℝ) (Adv : (Fin N → Cube n) → (Fin N → Cube n)),
      0 < ϵ → ϵ ≤ ϵ₀ → ν ∈ MeanBox n → IsCorruption ϵ Adv →
      otilde C ((n : ℝ) / ϵ ^ 2) ≤ N →
      (∀ S : Fin N → Cube n, ∀ s ∈ cReach P (classicalInput n N ϵ 0 S)
          ⌊C * ((N : ℝ) + 1) ^ C⌋₊, s.halted = true) ∧
      ∑ S : Fin N → Cube n, ENNReal.ofReal (∏ i, bern ν (S i)) *
        cRunLaw P (classicalInput n N ϵ 0 (Adv S)) ⌊C * ((N : ℝ) + 1) ^ C⌋₊
          {s | s.halted = false ∨ C * gHalf ϵ < Real.sqrt (∑ j, (outVec n s j - ν j) ^ 2)} ≤
        ENNReal.ofReal (1 / 100) := by sorry

end ProdMixedTomo.Supplement
