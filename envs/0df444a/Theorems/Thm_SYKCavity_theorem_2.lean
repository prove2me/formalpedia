-- Prove2me | Theorems.Thm_SYKCavity_theorem_2
-- name    : SYKCavity.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:09.328027+00:00
-- url     : https://prove2.me/theorems/056893b5-c6c8-47ab-8ed2-d1958874e734
-- title:
--   Theorem 2 — SYK thermal expectations $\mathrm{Tr}(Oe^{\beta H})/\mathrm{Tr}\,e^{\beta H}$ to error $N^{-c}$ with probability $1-N^{-a}$ in deterministic time $O(N^K)$ at every constant $\beta\ge0$
-- statement:
--   Fix $\beta\ge0$, a weight $w$ and exponents $a,c>0$. For $O=i^{w(w-1)/2}\psi_{i_1}\cdots\psi_{i_w}$ with $i_1<\dots<i_w$ let
--   $$f_O(\beta,J)=\frac{\operatorname{Tr}(Oe^{\beta H})}{\operatorname{Tr}e^{\beta H}}$$
--   for the SYK Hamiltonian (1.2) with independent standard Gaussian couplings. There is a deterministic classical algorithm which, with probability at least $1-N^{-a}$ over the Gaussian couplings, outputs $\hat f_O(\beta,J)$ with
--   $$|\hat f_O(\beta,J)-f_O(\beta,J)|\le N^{-c}\qquad(1.3)$$
--   in time at most $O(N^K)$, where $K$ depends only on $\beta,w,a,c$.
--
--   Precisely: there are $K,C$ and one admissible deterministic program $P$ such that for every $N\ge1$ and every such $O$, on every coupling vector $J$ the run on input $(N,w,i_1,\dots,i_w,\beta,J)$ halts within $C N^K$ steps, and the Gaussian measure of the couplings on which its output misses $f_O(\beta,J)$ by more than $N^{-c}$ is at most $N^{-a}$.
--
--   This is the paper's main quantum result: thermal expectations of the SYK model, conjectured to be classically hard, are computable in polynomial time at every constant temperature.
--
--   **Formalization Note** The machine is the published `SubsetConvFPRAS` unit-cost real RAM (rational literals, no coin, no oracle, no exponential or square-root instruction). The probability bound is on the outer measure of the failure set.
--
--   Differences from the source:
--   - reading: Majoranas ψ_i with {ψ_i, ψ_j} = 2δ_ij I (no representation fixed) → the first N Jordan–Wigner generators on ⌈N/2⌉ qubits, for every N ≥ 1; reason: for even N every representation is equivalent to this one; for odd N the page fixes none (its tr = 2^{−N/2} Tr presumes even N) and this register carries both irreducible representations
--   - reading: "with probability at least 1 − N^{−a}", no range of N → for every N ≥ 1; reason: Theorem 2 prints no "sufficiently large N" (Theorem 8 does); the program may treat finitely many N separately
--   - reading: "a deterministic classical algorithm … in time at most O(N^K)" → one Admissible, Deterministic program of the published unit-cost real RAM, the same for all N and all O of weight w, reading N, w, the sites, β and J, halting within C·N^K steps on every input; reason: the paper counts arithmetic operations ((4.40)); the RAM has rational literals only and no exp/√ instruction
--   - encoding: |f̂_O − f_O| ≤ N^{−c} with probability ≥ 1 − N^{−a} → the (outer) Gaussian measure of {J : the output y has ‖y − f_O‖ > N^{−c}} is ≤ N^{−a}, f_O the complex trace ratio; reason: f_O is real (O and e^{βH} are Hermitian); the outer measure needs no measurability of the failure set
--   - encoding: sites 1 ≤ i_1 < ⋯ < i_w ≤ N; couplings J_{i1i2i3i4} → an order embedding Fin w ↪o Fin N; J : {A ⊆ Fin N, |A| = 4} → ℝ; reason: 0-based indices
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Theorem 2, pp.4–5 ((1.2), p.4; (1.3), p.4)

import Mathlib
import Definitions.Def_SYKCavity_Majorana
import Definitions.Def_SYKCavity_Machine

open MeasureTheory

namespace SYKCavity

/-- **Theorem 2 (SYK thermal expectations)**, pp.4–5 of A. Schmidhuber, A. Zlokapa,
*Polynomial-time algorithms for mean-field models up to the glass transition*, arXiv:2610.06807
(held version, sha256 25d817ba…cfc5).

Fix `β ≥ 0`, a weight `w` and exponents `a, c > 0`. There are constants `K, C` and one deterministic
program `P` such that for every `N ≥ 1` and every observable `O = i^{w(w−1)/2} ψ_{i_1} ⋯ ψ_{i_w}`,
`i_1 < ⋯ < i_w`: on every coupling vector `J` the run halts within `C·N^K` steps, and the Gaussian
measure of the couplings on which the output `y` satisfies `|y − f_O(β, J)| > N^{−c}` is at most
`N^{−a}`, where `f_O(β, J) = Tr(O e^{βH}) / Tr e^{βH}` for the Hamiltonian (1.2).

**Formalization Note.**
* The algorithm is one `Admissible` (rational literals) and `Deterministic` (no coin, no oracle)
  program of the published `SubsetConvFPRAS` unit-cost real RAM; it reads `N`, `w`, the sites of `O`
  and the reals `β`, `J_A` from its input (`start`). `K` and `C` depend only on `β, w, a, c`.
* The running time bound `C·N^K` holds on every input; the probability bound is on the outer
  measure of the failure set, for every `N ≥ 1` (Theorem 2 has no "sufficiently large `N`").
* `f_O` is the complex ratio of traces (`fO`); it is real since `O` and `e^{βH}` are Hermitian, so the
  bound on `‖y − f_O‖` is the page's bound on `|f̂_O − f_O|`.
* `ψ_i` are the first `N` Jordan–Wigner Majoranas on `⌈N/2⌉` qubits (also for odd `N`). -/
theorem theorem_2 (β : ℝ) (hβ : 0 ≤ β) (w : ℕ) (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∃ (K C : ℕ) (P : SubsetConvFPRAS.Program), SubsetConvFPRAS.Admissible P ∧ Deterministic P ∧
      ∀ N : ℕ, 1 ≤ N → ∀ idx : Fin w ↪o Fin N,
        (∀ J : Quad N → ℝ, (outputAfter P N w idx β J (C * N ^ K)).isSome) ∧
        gaussLaw N {J | ∀ y : ℝ, outputAfter P N w idx β J (C * N ^ K) = some y →
            (N : ℝ) ^ (-c) < ‖(y : ℂ) - fO β N (obs N idx) J‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-a)) := by sorry

end SYKCavity
