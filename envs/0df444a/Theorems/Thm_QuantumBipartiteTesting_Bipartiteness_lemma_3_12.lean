-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_12
-- name    : QuantumBipartiteTesting.Bipartiteness.lemma_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:13:19.093561+00:00
-- url     : https://prove2.me/theorems/6f3928ad-d9d9-4593-828c-e407c76f2c33
-- title:
--   Lemma 3.12 — formal-to-feasible expectation error
-- statement:
--   There are positive absolute constants $C_1,c_1$, independent of the circuit and grid point. For each fixed positive query-band constant $B$, the following holds eventually for every $N$, every actual $q$-query circuit with $q\le BN^{1/3}/\log N$, every $(M,\ell)\in\mathcal G_N$ and both signing laws $\sigma$:
--   $$|p^{\rm feas}_\sigma-p^{\rm form}_\sigma|\le\exp(C_1q\log N-c_1N^{1/3}).$$
--   With the defined difference $\eta=\Delta-\Delta^{\rm form}$,
--   $$\Delta=\Delta^{\rm form}+\eta,\qquad |\eta|\le2\exp(C_1q\log N-c_1N^{1/3}).$$
--   There is a sufficiently small positive absolute $c_0$ for which $q\le c_0N^{1/3}/\log N$ implies uniform $\eta=o(1)$ over all circuits and grid points. The latter means that every positive tolerance has one eventual size threshold working for all these data. This compares two separately constructed functionals; their equality is not assumed.
--
--   Differences from the source:
--   - encoding: finite quantum query circuits with binary encoded outcomes and arbitrary workspace → published QueryAlg, arbitrary finite complex registers, injective null-zero bit encoding, unitary XOR oracle, input-independent output event; reason: every finite workspace is represented up to a basis bijection; unused answer bit strings and dummy vertex queries are retained
--   - reading: formal expectation described both by (A.2)–(A.4) and by arbitrary output on overflow → the algebraic partition functional (A.2)–(A.4), followed by signing probabilities and linear extension; reason: these descriptions disagree at N=M=4,l=2: a one-edge moment is 1/2 algebraically versus 1/8 with empty output on overflow; the feasible law stays conditional and its comparison remains a theorem
--   - reading: Definition 3.6 gives structural matching/response consistency and calls it equivalent to positive sampling probability → consistency is the structural condition, without a parameter-dependent positivity certificate; reason: a three-vertex two-color path is structurally consistent but cannot fit any block when N=M=4,l=2; retaining the structural definition preserves the full algebraic pattern domain
--   - encoding: q=O(N^(1/3)/log N) and uniform o(1) → quantified positive band B with an eventual threshold, and an arbitrary positive tolerance uniformly over circuits and grid pairs; reason: retains the source asymptotic quantifier order and both error clauses
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Lemma 3.12, PDF = printed page 17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset

theorem lemma_3_12 :
    (∃ C₁ c₁ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ ∀ B : ℝ, 0 < B → ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ k w q : ℕ, (q : ℝ) ≤ B * LowerBoundScale N →
      ∀ E : Encoding (Fin N × Bool) k, ∀ A : Algorithm (Address N 3) k w q,
      ∀ out : (Address N 3 × Bits k) × Fin w → Bool, ∀ M l : ℕ, Grid N M l →
        (∀ s : Signing, |FeasibleAcceptance E A out s M l - FormalAcceptance E A out s M l| ≤
          Real.exp (C₁*q*Real.log N - c₁*(N : ℝ)^(1/3 : ℝ))) ∧
        FeasibleGap E A out M l = FormalGap E A out M l + GapError E A out M l ∧
        |GapError E A out M l| ≤ 2*Real.exp (C₁*q*Real.log N - c₁*(N : ℝ)^(1/3 : ℝ))) ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧ UniformGapVanishing c₀) := by sorry

end QuantumBipartiteTesting.Bipartiteness
