-- Prove2me | Theorems.Thm_TwoFoldOPI_Supplement_theorem_8_5
-- name    : TwoFoldOPI.Supplement.theorem_8_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:08:53.61766+00:00
-- url     : https://prove2.me/theorems/db5dc578-df60-4964-b514-c31be9d8e189
-- title:
--   Theorem 8.5 — classical algorithm for randomly punctured Reed–Muller codes
-- statement:
--   Fix an odd prime power $q$ and real constants $\rho\in(0,q-1)$ and $c>1$ with
--   $$c>\frac{\max\{\mathrm{CntExp}_q(3\rho),\ \mathrm{CntExp}_q(\rho)+\rho/(q-1)\}}{\mathrm{CntExp}_q(\rho)} .\tag{18}$$
--   Let $r=\lfloor\rho v\rfloor$, $n=\mathrm{Count}_q(v,r)$, $m=\min(\lfloor n^c\rfloor,q^v)$, and let $S\subseteq\mathbb F_q^v$ be a uniformly random $m$-element set. Then there is a classical algorithm for $\mathrm{RMSyndrome}_{q,\rho,c}(v)$, running in time $\mathrm{poly}(m)$, such that, as $v\to\infty$, with probability $1-o(1)$ over $S$ it outputs a solution (a vector $y$ with no zero entry and $By=0$) with probability $1-o(1)$ over its internal randomness. The same guarantee holds for $\mathrm{RMSupp}_{q,\rho,c}(v)$.
--
--   This classical counterpart of Theorem 7.5 uses the Schur cube instead of the Schur square, hence the threshold with $3\rho$ in place of $2\rho$.
--
--   Differences from the source:
--   - reading: with probability 1 − o(1) over S, the algorithm succeeds with probability 1 − o(1), as v → ∞ → there are functions g, h tending to 0 such that, for every v, with probability at least 1 − h(v) over S the success probability is at least 1 − g(v); one program and one polynomial for all v; reason: the two limits are kept separate, as printed
--   - generalization: the algorithm is given the random set S → the guarantee holds for every listing of the points of S; reason: specializes to any fixed order
--   - generalization: a fixed explicitly represented field F_q → one program for every explicit presentation of F_q, given as part of the input; reason: specializes to any fixed presentation
--   - reading: RMSupp asks for a polynomial f of total degree at most v(q − 1) − ⌊ρv⌋ − 1 → the output is the coefficient vector of f over the reduced monomials, in the order of finFunctionFinEquiv; reason: the source does not fix an output format; every solution reduces to this form
--   - encoding: a classical algorithm running in time poly(m), probability over its internal randomness → a randomized bit program (QAlgorithms.OPI.BitOracleProgram, fair coins, constant oracle) on the input encoding that halts within P(m) transitions on every coin sequence; success means halting accepting with an output whose first symbols form a solution; reason: a standard classical machine model; coins are the internal randomness
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §8.3, Theorem 8.5, p. 48

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIBitPrograms
import Definitions.Def_TwoFoldOPI_elemBits
import Definitions.Def_TwoFoldOPI_decodeWord
import Definitions.Def_TwoFoldOPI_Supplement_rmCount
import Definitions.Def_TwoFoldOPI_Supplement_countExp
import Definitions.Def_TwoFoldOPI_Supplement_RMInput
import Definitions.Def_TwoFoldOPI_Supplement_rmSyndromeSolves
import Definitions.Def_TwoFoldOPI_Supplement_rmSuppSolves

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms QAlgorithms.OPI Filter Topology

open Classical in
/-- **Theorem 8.5 (classical algorithm for randomly punctured Reed–Muller codes).**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §8.3, Theorem 8.5, p.48: "Fix an odd prime power q and real constants ρ ∈ (0, q − 1) and
c > 1 such that: c > max{CntExp_q(3ρ), CntExp_q(ρ) + ρ/(q − 1)} / CntExp_q(ρ). (18) Here CntExp_q is
the counting exponent of Definition 5.10. Then there is a classical algorithm for
RMSyndrome_{q,ρ,c}(v), running in time poly(m) for m = min(⌊n^c⌋, q^v) as in Definition 6.1, with
the following guarantee: with probability 1 − o(1) over the uniformly random m-element subset
S ⊆ F_q^v, the algorithm outputs a solution with probability 1 − o(1) over its internal randomness,
as v → ∞. Consequently, the same guarantee holds for RMSupp_{q,ρ,c}(v) by Lemma 6.4.";
Definitions 6.1–6.2, p.36.

With `r = ⌊ρv⌋`, `n = Count_q(v, r)`, `m = min(⌊n^c⌋, q^v)`:
1. (RMSyndrome) there are a classical randomized bit program `A`, a polynomial `P` and
   functions `g, h → 0` such that for every presentation `F` of `F_q` and every `v`: on every input
   `(F, v, m, pts)` and every coin sequence `A` halts within `P(m)` transitions; and with
   probability at least `1 − h(v)` over the uniform `m`-subset `S ⊆ F^v`, for every listing `pts` of
   `S`, `A` halts accepting with an output whose first `m` symbols form `y` with no zero entry and
   `By = 0`, with probability at least `1 − g(v)` over its coins;
2. (RMSupp) the same holds for a program `A'` whose output is the coefficient vector (over reduced
   monomials, `X^α` at position `finFunctionFinEquiv α`) of a polynomial of total degree at most
   `v(q − 1) − r − 1` nonzero exactly on `S`.

**Formalization Note.** A classical randomized algorithm is a `QAlgorithms.OPI.BitOracleProgram`
(bit tapes, fair coins; its oracle is the constant `0` and carries no information), run on
`RMInput.encode`; "time" is the number of transitions, and its internal randomness is the coin tape
(`bitExecutionLaw`). Its output string is read symbol by symbol (`decodeWord`, missing bits read as
`0`). The two `1 − o(1)` limits are `g` and `h`, with one program and one polynomial for all `v`;
every listing of `S` is covered. `CntExp_q` is `countExp q`. The trivial case `m = q^v` is
included. -/
theorem theorem_8_5 (q : ℕ) (hq : IsPrimePow q) (hodd : Odd q) (ρ c : ℝ) (hρ0 : 0 < ρ)
    (hρ1 : ρ < (q : ℝ) - 1) (hc : 1 < c)
    (h18 : max (countExp q (3 * ρ)) (countExp q ρ + ρ / ((q : ℝ) - 1)) / countExp q ρ < c) :
    (∃ (A : BitOracleProgram) (P : Polynomial ℕ) (g h : ℕ → ℝ),
      Tendsto g atTop (𝓝 0) ∧ Tendsto h atTop (𝓝 0) ∧
        ∀ F : AvgCaseTI.FieldPres, Fintype.card F.F = q → ∀ v : ℕ,
          (∀ (pts : Fin (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v)) → Fin v → F.F)
              (coins : ℕ → Bool),
            (bitProgramExecution A (RMInput.encode ⟨F, v, _, pts⟩) (fun _ => false) coins
              (P.eval (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v)))).status.isSome) ∧
          1 - h v ≤ ((((Finset.univ : Finset (Fin v → F.F)).powersetCard
              (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v))).filter fun S =>
                ∀ pts : Fin (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v)) → Fin v → F.F,
                  Function.Injective pts → Set.range pts = ↑S →
                  1 - g v ≤ ((bitExecutionLaw A (RMInput.encode ⟨F, v, _, pts⟩) (fun _ => false)
                    (P.eval (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v)))).toOuterMeasure
                      {s | s.status = some true ∧
                        rmSyndromeSolves ⌊ρ * v⌋₊ pts
                          (decodeWord F _ fun i => s.output.getD i.val false)}).toReal).card : ℝ) /
            (((Finset.univ : Finset (Fin v → F.F)).powersetCard
              (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v))).card : ℝ)) ∧
    (∃ (A : BitOracleProgram) (P : Polynomial ℕ) (g h : ℕ → ℝ),
      Tendsto g atTop (𝓝 0) ∧ Tendsto h atTop (𝓝 0) ∧
        ∀ F : AvgCaseTI.FieldPres, Fintype.card F.F = q → ∀ v : ℕ,
          (∀ (pts : Fin (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v)) → Fin v → F.F)
              (coins : ℕ → Bool),
            (bitProgramExecution A (RMInput.encode ⟨F, v, _, pts⟩) (fun _ => false) coins
              (P.eval (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v)))).status.isSome) ∧
          1 - h v ≤ ((((Finset.univ : Finset (Fin v → F.F)).powersetCard
              (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v))).filter fun S =>
                ∀ pts : Fin (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v)) → Fin v → F.F,
                  Function.Injective pts → Set.range pts = ↑S →
                  1 - g v ≤ ((bitExecutionLaw A (RMInput.encode ⟨F, v, _, pts⟩) (fun _ => false)
                    (P.eval (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v)))).toOuterMeasure
                      {s | s.status = some true ∧
                        rmSuppSolves v ⌊ρ * v⌋₊ (↑S : Set (Fin v → F.F)) fun α =>
                          decodeWord F (Fintype.card F.F ^ v) (fun i => s.output.getD i.val false)
                            (finFunctionFinEquiv α)}).toReal).card : ℝ) /
            (((Finset.univ : Finset (Fin v → F.F)).powersetCard
              (min ⌊(rmCount q v ⌊ρ * v⌋₊ : ℝ) ^ c⌋₊ (q ^ v))).card : ℝ)) := by sorry

end Supplement

end TwoFoldOPI
