-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_Supplement_theorem_4_1
-- name    : QuantumBipartiteTesting.Bipartiteness.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:20:01.151748+00:00
-- url     : https://prove2.me/theorems/07d66685-63f4-49f9-9c1e-5cfe76e04d62
-- title:
--   Theorem 4.1 — Quantum expansion testing needs Ω(N^(1/3)/(log N)^(4/3)) queries
-- statement:
--   For every fixed degree bound $d\ge4$, there is $\alpha_0(d)\in(0,1)$ such that for every $0<\alpha'\le\alpha\le\alpha_0(d)$ there is $\varepsilon_0(\alpha,\alpha',d)\in(0,1)$ with the following property. For every fixed $0<\varepsilon\le\varepsilon_0$, there are $C>0$ and $N_0\ge2$ such that, for every integer $N\ge N_0$, every two-sided quantum tester which accepts every $\alpha$-vertex-expander and rejects every graph $\varepsilon$-far from $\alpha'$-vertex-expansion, each with probability at least $2/3$, satisfies
--   $$q\ge C\,\frac{N^{1/3}}{(\ln N)^{4/3}}.$$
--   Correctness ranges over all simple graphs of maximum degree at most $d$ and every packed adjacency ordering. Arbitrary finite complex workspace and injective binary response encodings are included. Every sufficiently large final size is covered, including nonproducts of intermediate size and color count; $\alpha'=\alpha$ is included. This is the paper's independent companion theorem, not a prerequisite for the published bipartiteness goal.
--
--   Differences from the source:
--   - encoding: vertices [n] and asymptotic notation → Fin n, natural logarithms and explicit uniform constants/thresholds; reason: bijective vertex labeling and logarithm-base changes preserve all source instances
--   - reading: Remark 2.6 prints alpha at most alpha-prime, whereas both formal Theorem 4.1 statements print alpha-prime at most alpha → alpha-prime at most alpha, including equality, with the remarks' small-fixed-parameter convention; reason: pp.21 and 27 agree with the proof; the positive YES constant is chosen above the final threshold
--   - encoding: bounded fixed degree and sufficiently small fixed parameters → d at least 4, alpha0 before alpha,alpha-prime, epsilon0 before epsilon, and C,N0 before N and tester; reason: the degree-four hard instances work for all fixed larger d with normalization epsilon*d*N; this expands the standing conventions without assuming hardness
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Theorem 4.1, printed page = PDF page 21; repeated with proof p.27

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Unsigned

namespace QuantumBipartiteTesting.Bipartiteness.Supplement
open Finset

/-- The formal theorem's α' ≤ α ordering is used, with the small-parameter
convention of Remarks 2.4 and 2.6. The two printed formal statements agree. -/
theorem theorem_4_1 (d : ℕ) (hd : 4 ≤ d) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ α₀ < 1 ∧ ∀ α α' : ℝ,
      0 < α' → α' ≤ α → α ≤ α₀ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
          ∀ k w q : ℕ, ∀ E : Encoding (Fin N) k,
          ∀ A : Algorithm (Address N d) k w q,
          ∀ out : (Address N d × Bits k) × Fin w → Bool,
            ExpansionTester ε α α' E A out → C * ExpansionScale N ≤ (q : ℝ) := by sorry

end QuantumBipartiteTesting.Bipartiteness.Supplement
