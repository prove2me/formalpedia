-- Prove2me | Theorems.Thm_ReplParity_proposition_3_4
-- name    : ReplParity.proposition_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:44:18.898601+00:00
-- url     : https://prove2.me/theorems/81b058be-beb3-470d-87ca-18253ba95674
-- title:
--   Proposition 3.4 — multistage covering subspace (statistical clauses, for the construction of its proof)
-- statement:
--   There is an absolute constant $C$ such that for every $n\ge1$, all $0<\varepsilon,\rho<1$ and every admissible implementation of the token min-hash in the stages, the multistage cover of the proof satisfies:
--
--   1. its sample size is $\sum_{j=1}^{L}\big(N_g(q_j,\eta_j)+R_j\big)\le C\,\dfrac{n^3}{\varepsilon\rho^2}$;
--   2. its output $U$ lies in the span of the samples, for every sample and every seed;
--   3. for every distribution $Q$ on $\mathbb F_2^n$,
--   $$\Pr\big[Q(\mathbb F_2^n\setminus U)>\varepsilon/4\big]<\frac{\rho}{16}\qquad\text{and}\qquad \Pr\big[U(S;r)\ne U(S';r)\big]<\frac{\rho}{8},$$
--   where $S,S'\sim Q^m$ are independent and the seed $r$ is shared.
--
--   Differences from the source:
--   - reading: "polynomial-time" (Proposition 3.4) → carried by ReplParity.theorem_3_6's TM2 polynomial-time clause, not stated here; reason: explicit degrees and exact real block sizes depend on a bit-cost RAM the paper does not pin down; only polynomiality is model-robust, and the goal's proof uses only that (paper.md decision 6)
--   - reading: there is a finite-bit algorithm → the finite-bit algorithm of the proof, for every admissible implementation; reason: the construction witnesses the existential; the statement is about it so that solvers formalize the paper's algorithm
--   - generalization: the field 𝔽_{2^b} with b the least power of two ≥ max{B₀, ⌈log₂(8K²/η)⌉}, its reading as a b-bit integer, the reduced-row-echelon token encoding and the canonical subspace order → any finite field with a bijection to b-bit integers and 2^b ≥ 8K²/η, any token encoding injective on tokens (V, j) with j ≤ K, any injective subspace code (TokenHashImpl); reason: the paper's choices are one instance; B₀ only guarantees that an injective encoding exists
--   - reading: For every distribution Q … there is an algorithm → one construction serving every Q, quantified after it; reason: the construction does not depend on Q; this is the stronger reading (paper.md decision 7)
--   - generalization: rational parameters (finite-bit model, §2.2) → real parameters; reason: every rational is real, so the statement specializes to the paper's
--   - reading: n unrestricted (the proposition calls Lemma 3.2, stated for n ≥ 1) → 1 ≤ n; reason: at n = 0 the construction still draws the gate's ⌈512/(q₁η₁²)⌉ ≥ 1 samples while C·n³/(ερ²) = 0; the paper uses n = d + 1 ≥ 2 (paper.md decision 8)
--   - reading: the span of the samples it uses → the span of all m input samples; reason: every block is reserved in advance and counted in m, so the algorithm's samples are the whole input
--   - encoding: O(·) → ∃ C before n and the parameters; reason: §2, p.10: constants inside O(·) are absolute
--   - encoding: probabilities over S, S′ ∼ Q^m and a seed of unbiased bits → finite sums over samples weighted by ∏ Q(Sᵢ) and over a seed uniform on the product of the stages' finite seed sets; reason: the seed sets have power-of-two sizes, so the uniform seed is the uniform bit string read in blocks; same events and probabilities
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Proposition 3.4, p.17 (PDF p.19) and its proof

import Mathlib
import Definitions.Def_ReplParity_multistageCover
import Definitions.Def_ReplParity_prIID
import Definitions.Def_ReplParity_massOutside

namespace ReplParity

/-- **Proposition 3.4 (Multistage covering subspace), statistical clauses, for the construction of its
proof.** Shen, Zhong, *Replicable Parity Learning: Cubic Sample Complexity and a Geometric
Characterization*, STOC 2027 submission (manuscript sha256 40424491…), Proposition 3.4, p.17 (PDF
p.19): "For every distribution Q on 𝔽ⁿ₂ and all 0 < ε, ρ < 1, there is a polynomial-time finite-bit
algorithm with O(n³/(ερ²)) samples whose output U lies in the span of the samples it uses and
satisfies Pr[Q(𝔽ⁿ₂ \ U) > ε/4] < ρ/16 and Pr[U(S; r) ≠ U(S′; r)] < ρ/8."

The algorithm is `multistageCover impl` of the proof (stages `j = 1, …, L`, each a gate, a
collection block and Lemma 3.2's construction with implementation `impl j`); its sample size is
`coverM n ε ρ = Σ_j (N_g(q_j, η_j) + R_j)`, and the seed is uniform. There is an absolute constant
`C` such that, for every `n ≥ 1`, `0 < ε, ρ < 1` and every admissible `impl`: the sample size is at
most `C n³/(ερ²)`; `U ⊆ span(S)` for every sample and seed; and for every distribution `Q` on 𝔽ⁿ₂
both probability bounds hold, strictly. -/
theorem proposition_3_4 :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ ε ρ : ℝ, 0 < ε → ε < 1 → 0 < ρ → ρ < 1 →
      ∀ impl : (j : ℕ) → TokenHashImpl n (stageK n ε ρ j) (stageEta ε ρ j),
        (coverM n ε ρ : ℝ) ≤ C * ((n : ℝ) ^ 3 / (ε * ρ ^ 2)) ∧
        (∀ (S : Fin (coverM n ε ρ) → Vec n) (seed : CoverSeed n ε ρ impl),
          multistageCover impl S seed ≤ Submodule.span (ZMod 2) (Set.range S)) ∧
        ∀ Q : PMF (Vec n),
          prIID Q (coverM n ε ρ) (fun S (seed : CoverSeed n ε ρ impl) =>
            ε / 4 < massOutside Q (multistageCover impl S seed)) < ρ / 16 ∧
          prIID2 Q (coverM n ε ρ) (fun S S' (seed : CoverSeed n ε ρ impl) =>
            multistageCover impl S seed ≠ multistageCover impl S' seed) < ρ / 8 := by sorry

end ReplParity
