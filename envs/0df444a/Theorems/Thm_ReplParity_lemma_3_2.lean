-- Prove2me | Theorems.Thm_ReplParity_lemma_3_2
-- name    : ReplParity.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:41:59.85942+00:00
-- url     : https://prove2.me/theorems/6478119b-30bd-474f-8b3e-884152b22738
-- title:
--   Lemma 3.2 (i)–(iii) — token min-hash (for the construction of its proof)
-- statement:
--   Let $n\ge1$, $0<\eta<1$ and $K=4\lceil128n^3/\eta^2\rceil$. For every admissible implementation (finite field $F$ with $2^b\ge8K^2/\eta$ elements read as $b$-bit integers, injective token encoding, injective subspace code) and every distribution $Q$ on the nonzero vectors of $\mathbb F_2^n$, the token min-hash construction $W(S;c)$ of the proof, with a uniform seed $c\in F^{K/2}$, satisfies:
--
--   1. (replicability) $\Pr[W(S;c)\ne W(S';c)]\le\eta$ for independent $S,S'\sim Q^K$ and a shared seed $c$;
--   2. (coverage) $\Pr\big[Q(\mathbb F_2^n\setminus W)>1/2\big]\le\eta$;
--   3. (containment) $W\subseteq\mathrm{span}(S)$ for every sample $S\in(\mathbb F_2^n)^K$ and every seed.
--
--   Differences from the source:
--   - reading: "Its running time is O(K²n³ + K²b³ + b⁵), where b = O(n² + log K + log(1/η))" → carried by ReplParity.theorem_3_6's TM2 polynomial-time clause, not stated here; reason: explicit degrees and exact real block sizes depend on a bit-cost RAM the paper does not pin down; only polynomiality is model-robust, and the goal's proof uses only that (paper.md decision 6)
--   - reading: there is a finite-bit algorithm → the finite-bit algorithm of the proof, for every admissible implementation; reason: the construction witnesses the existential; the statement is about it so that solvers formalize the paper's algorithm
--   - generalization: the field 𝔽_{2^b} with b the least power of two ≥ max{B₀, ⌈log₂(8K²/η)⌉}, its reading as a b-bit integer, the reduced-row-echelon token encoding and the canonical subspace order → any finite field with a bijection to b-bit integers and 2^b ≥ 8K²/η, any token encoding injective on tokens (V, j) with j ≤ K, any injective subspace code (TokenHashImpl); reason: the paper's choices are one instance; B₀ only guarantees that an injective encoding exists
--   - generalization: rational parameters (finite-bit model, §2.2) → real parameters; reason: every rational is real, so the statement specializes to the paper's
--   - generalization: (iii) for every sample (drawn from the nonzero vectors) → (iii) for every S ∈ (𝔽ⁿ₂)^K, zero vectors allowed; reason: covers every sample of the source
--   - encoding: a distribution Q on the nonzero vectors of 𝔽ⁿ₂; seed c_0, …, c_{2κ−1} independent uniform → Q a distribution on 𝔽ⁿ₂ with Q(0) = 0; c uniform on F^{K/2} (2κ = K/2); reason: same distributions
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Lemma 3.2, p.15 (PDF p.17) and its proof, p.16

import Mathlib
import Definitions.Def_ReplParity_tokenMinHash
import Definitions.Def_ReplParity_prIID
import Definitions.Def_ReplParity_massOutside

namespace ReplParity

/-- **Lemma 3.2 (Token min-hash) (i)–(iii), for the construction of its proof.** Shen, Zhong,
*Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027
submission (manuscript sha256 40424491…), Lemma 3.2, p.15 (PDF p.17): "For every n ≥ 1 and
0 < η < 1, let K = 4⌈128n³/η²⌉. There is a finite-bit algorithm that receives K samples from a
distribution Q on the nonzero vectors of 𝔽ⁿ₂ and outputs a subspace W with the following
properties. (i) (replicability) Pr[W(S; r) ≠ W(S′; r)] ≤ η for independent S, S′ ∼ Q^K and a shared
seed r. (ii) (coverage) Pr[Q(𝔽ⁿ₂ \ W) > 1/2] ≤ η. (iii) (containment) W ⊆ span(S) for every sample
and every seed."

The algorithm is `tokenMinHash H` of the proof (p.16), for every admissible implementation `H`
(field of size `2^b ≥ 8K²/η`, integer reading, injective token encoding, subspace order); the seed
is uniform on `F^{K/2}`. -/
theorem lemma_3_2 (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (H : TokenHashImpl n (tokK n η) η) (Q : PMF (Vec n)) (hQ : Q 0 = 0) :
    prIID2 Q (tokK n η) (fun S S' (c : Fin (tokK n η / 2) → H.F) =>
        tokenMinHash H S c ≠ tokenMinHash H S' c) ≤ η ∧
    prIID Q (tokK n η) (fun S (c : Fin (tokK n η / 2) → H.F) =>
        1 / 2 < massOutside Q (tokenMinHash H S c)) ≤ η ∧
    ∀ (S : Fin (tokK n η) → Vec n) (c : Fin (tokK n η / 2) → H.F),
      tokenMinHash H S c ≤ Submodule.span (ZMod 2) (Set.range S) := by sorry

end ReplParity
