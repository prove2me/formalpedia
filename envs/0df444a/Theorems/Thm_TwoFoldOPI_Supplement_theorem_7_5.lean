-- Prove2me | Theorems.Thm_TwoFoldOPI_Supplement_theorem_7_5
-- name    : TwoFoldOPI.Supplement.theorem_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:07:29.079409+00:00
-- url     : https://prove2.me/theorems/a11e870f-aecd-48ef-b751-8f67f076c838
-- title:
--   Theorem 7.5 — quantum algorithm for randomly punctured Reed–Muller codes
-- statement:
--   Fix a prime power $q>2$ and real constants $\rho\in(0,q-1)$ and $c>1$ with
--   $$c>\frac{\max\{\mathrm{CntExp}_q(2\rho),\ \mathrm{CntExp}_q(\rho)+\rho/(q-1)\}}{\mathrm{CntExp}_q(\rho)} .\tag{12}$$
--   Let $r=\lfloor\rho v\rfloor$, $n=\mathrm{Count}_q(v,r)$ and $m=\min(\lfloor n^c\rfloor,q^v)$, and let $S\subseteq\mathbb F_q^v$ be a uniformly random $m$-element set. Then there is a quantum algorithm for $\mathrm{RMSyndrome}_{q,\rho,c}(v)$ — find $y\in\mathbb F_q^m$ with no zero entry and $By=0$, where $B$ evaluates the reduced monomials of total degree at most $r$ at the points of $S$ — running in time $\mathrm{poly}(m)$, such that, as $v\to\infty$, with probability $1-o(1)$ over $S$ the algorithm outputs a solution with probability $1-o(1)$ over its internal measurements. The same guarantee holds for $\mathrm{RMSupp}_{q,\rho,c}(v)$: find a polynomial of total degree at most $v(q-1)-r-1$ that is nonzero exactly on $S$.
--
--   This applies the two-fold Schur-square algorithm of Theorem 7.4 to the shortened Reed–Muller code; it gives an efficient quantum algorithm for a code-search problem in a regime where no classical algorithm is known (compare Theorem 8.5, which needs the stronger threshold (18)).
--
--   Differences from the source:
--   - reading: with probability 1 − o(1) over S, the algorithm succeeds with probability 1 − o(1), as v → ∞ → there are functions g, h tending to 0 such that, for every v, with probability at least 1 − h(v) over S the success probability is at least 1 − g(v); one algorithm and one polynomial for all v; reason: the two limits are kept separate, as printed
--   - generalization: the algorithm is given the random set S → the guarantee holds for every listing of the points of S (every column order of B); reason: the source does not fix an order; the statement for every order specializes to any fixed one
--   - generalization: a fixed explicitly represented field F_q → one algorithm for every explicit presentation of F_q, given as part of the input; reason: specializes to any fixed presentation
--   - reading: RMSupp asks for a polynomial f of total degree at most v(q − 1) − ⌊ρv⌋ − 1 → the output is the coefficient vector of f over the reduced monomials X^α, α ∈ {0, …, q−1}^v, in the order of finFunctionFinEquiv; reason: the source does not fix an output format; every solution reduces to this form without raising the degree
--   - encoding: a quantum algorithm running in time poly(m) → a uniform family of Clifford+T programs (QAlgorithms.OPI.UniformResourceFamily) whose charged resources are at most P(m) on every input; reason: the base mission's algorithm model
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.4, Theorem 7.5, p. 41

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
import Definitions.Def_QAlgorithms_Defs_OPIUniformity
import Definitions.Def_TwoFoldOPI_elemBits
import Definitions.Def_TwoFoldOPI_decodeWord
import Definitions.Def_TwoFoldOPI_Supplement_readBits
import Definitions.Def_TwoFoldOPI_Supplement_rmCount
import Definitions.Def_TwoFoldOPI_Supplement_countExp
import Definitions.Def_TwoFoldOPI_Supplement_RMInput
import Definitions.Def_TwoFoldOPI_Supplement_rmSyndromeSolves
import Definitions.Def_TwoFoldOPI_Supplement_rmSuppSolves

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms QAlgorithms.OPI Filter Topology

open Classical in
/-- **Theorem 7.5 (quantum algorithm for randomly punctured Reed–Muller codes).**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.4, Theorem 7.5, p.41: "Fix a prime power q > 2 and real constants ρ ∈ (0, q − 1) and
c > 1 such that: c > max{CntExp_q(2ρ), CntExp_q(ρ) + ρ/(q − 1)} / CntExp_q(ρ). (12) Here CntExp_q is
the counting exponent of Definition 5.10. Then there is a quantum algorithm for
RMSyndrome_{q,ρ,c}(v), running in time poly(m) for m = min(⌊n^c⌋, q^v) as in Definition 6.1, with
the following guarantee: with probability 1 − o(1) over the uniformly random m-element subset
S ⊆ F_q^v, the algorithm outputs a solution with probability 1 − o(1) over its internal
measurements, as v → ∞. Consequently, the same guarantee holds for RMSupp_{q,ρ,c}(v) by Lemma 6.4.";
Definitions 6.1–6.2, p.36 (`n = Count_q(v, ⌊ρv⌋)`, `m = min(⌊n^c⌋, q^v)`).

With `r = ⌊ρv⌋`, `n = Count_q(v, r)`, `m = min(⌊n^c⌋, q^v)`:
1. (RMSyndrome) there are a uniform quantum algorithm `A` (output: `m` field symbols), a
   polynomial `P` and functions `g, h → 0` such that for every presentation `F` of `F_q` and every
   `v`: on every input `(F, v, m, pts)` the charged resources are at most `P(m)`; and with
   probability at least `1 − h(v)` over the uniform `m`-subset `S ⊆ F^v`, for every listing `pts`
   of `S`, `A` outputs `y` with no zero entry and `By = 0` with probability at least `1 − g(v)`;
2. (RMSupp) the same holds for an algorithm `A'` whose output is the coefficient vector (over
   reduced monomials `X^α`, `α ∈ {0, …, q−1}^v`, at position `finFunctionFinEquiv α`) of a
   polynomial of total degree at most `v(q − 1) − r − 1` nonzero exactly on `S`.

**Formalization Note.** "1 − o(1) … with probability 1 − o(1)" is two separate limits, `g` and
`h`, with one algorithm and one polynomial for all `v` (and all presentations of `F_q`, the field
being part of the input). The guarantee holds for every order in which the points of `S` are
listed (the column order of `B`). Probabilities over `S` are ratios of counts of `m`-subsets.
Algorithms are `QAlgorithms.OPI.UniformResourceFamily`s (Clifford+T, measurements, coins, no
oracle). `CntExp_q` is `countExp q`; `Count_q` is `rmCount`. The trivial case `m = q^v` (Remark 6.3)
is included. -/
theorem theorem_7_5 (q : ℕ) (hq : IsPrimePow q) (hq2 : 2 < q) (ρ c : ℝ) (hρ0 : 0 < ρ)
    (hρ1 : ρ < (q : ℝ) - 1) (hc : 1 < c)
    (h12 : max (countExp q (2 * ρ)) (countExp q ρ + ρ / ((q : ℝ) - 1)) / countExp q ρ < c) :
    (∃ A : UniformResourceFamily RMInput RMInput.encode RMInput.scale,
      (∀ x, (A.construct x).oracles = 0 ∧ (A.construct x).outputBits = x.m * bitsPerSymbol x.F) ∧
      ∃ (P : Polynomial ℕ) (g h : ℕ → ℝ), Tendsto g atTop (𝓝 0) ∧ Tendsto h atTop (𝓝 0) ∧
        ∀ F : AvgCaseTI.FieldPres, Fintype.card F.F = q → ∀ v : ℕ,
          (∀ pts : Fin (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v)) → Fin v → F.F,
            membershipResources (A.construct ⟨F, v, _, pts⟩).program (fun _ => 1) ≤
              P.eval (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v))) ∧
          1 - h v ≤ ((((Finset.univ : Finset (Fin v → F.F)).powersetCard
              (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v))).filter fun S =>
                ∀ pts : Fin (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v)) → Fin v → F.F,
                  Function.Injective pts → Set.range pts = ↑S →
                  1 - g v ≤ membershipOutputLaw (A.construct ⟨F, v, _, pts⟩).program (fun _ => 1)
                    (fun o => ∃ bits, o = some bits ∧
                      rmSyndromeSolves ⌊ρ * v⌋₊ pts (decodeWord F _ (readBits bits)))).card : ℝ) /
            (((Finset.univ : Finset (Fin v → F.F)).powersetCard
              (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v))).card : ℝ)) ∧
    (∃ A : UniformResourceFamily RMInput RMInput.encode RMInput.scale,
      (∀ x, (A.construct x).oracles = 0 ∧
        (A.construct x).outputBits = Fintype.card x.F.F ^ x.v * bitsPerSymbol x.F) ∧
      ∃ (P : Polynomial ℕ) (g h : ℕ → ℝ), Tendsto g atTop (𝓝 0) ∧ Tendsto h atTop (𝓝 0) ∧
        ∀ F : AvgCaseTI.FieldPres, Fintype.card F.F = q → ∀ v : ℕ,
          (∀ pts : Fin (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v)) → Fin v → F.F,
            membershipResources (A.construct ⟨F, v, _, pts⟩).program (fun _ => 1) ≤
              P.eval (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v))) ∧
          1 - h v ≤ ((((Finset.univ : Finset (Fin v → F.F)).powersetCard
              (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v))).filter fun S =>
                ∀ pts : Fin (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v)) → Fin v → F.F,
                  Function.Injective pts → Set.range pts = ↑S →
                  1 - g v ≤ membershipOutputLaw (A.construct ⟨F, v, _, pts⟩).program (fun _ => 1)
                    (fun o => ∃ bits, o = some bits ∧
                      rmSuppSolves v ⌊ρ * v⌋₊ (↑S : Set (Fin v → F.F)) fun α =>
                        decodeWord F (Fintype.card F.F ^ v) (readBits bits)
                          (finFunctionFinEquiv α))).card : ℝ) /
            (((Finset.univ : Finset (Fin v → F.F)).powersetCard
              (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v))).card : ℝ)) := by sorry

end Supplement

end TwoFoldOPI
