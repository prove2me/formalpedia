-- Prove2me | Theorems.Thm_PairwiseRealize_eq_A_1_A_3_accepted_law
-- name    : PairwiseRealize.eq_A_1_A_3_accepted_law
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:43.506089+00:00
-- url     : https://prove2.me/theorems/45547bbc-81e5-463f-946f-e078ca389f6d
-- title:
--   (A.1)–(A.3), p.10 — the deletion-conditioned law of a bundle: acceptance $\ge p_*$, endpoint masses $<2/N$, and the moment bound
-- statement:
--   Let $p_*=1023/1024$ and $|D|\le N/4096$.
--
--   1. Each of the four endpoints of a raw rectangular bundle on disjoint nonempty $A,B$ is uniform on $V$.
--   2. More generally, let a raw bundle be uniform on a finite nonempty set, with $a\le4$ endpoints, each uniform on $V$. Then:
--      - (A.1) $\mathbb P(E_D)\ge p_*$, where $E_D$ is the event that all endpoints avoid $D$;
--      - (A.2) for every endpoint $X$ and every $x$, $\mathbb P(X=x\mid E_D)\le\frac1{p_*N}<\frac2N$;
--      - (A.3) $\mathbb E(X_C\mid E_D)\preceq\frac a{p_*}I_m$, and $\|X_C\|\le4m$ for every bundle, with $X_C=\sum_{x\in C}v_xv_x^{\mathsf T}$.
--
--   These bounds show that deletion costs only a constant factor in dispersion and in the matrix mean.
--
--   Differences from the source:
--   - generalization: bundles of the reserve, a = |C| ≤ 4 endpoints → any finite uniform bundle type with a ≤ 4 endpoints each uniform on V, repetitions allowed; reason: covers rectangles, total triples, coordinate edges and faces, which part 1 and the corresponding counts specialize to
--   - encoding: probabilities and conditional expectations → counting ratios over the raw and accepted sets; ⪯ as positive semidefiniteness of the difference; ‖·‖ the spectral norm; reason: the laws are uniform on finite sets
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §A.1, (A.1)–(A.3), p.10 (PDF p.11)

import Mathlib
import Definitions.Def_PairwiseRealize_Model
import Definitions.Def_PairwiseRealize_Bundles

open scoped Matrix.Norms.L2Operator

namespace PairwiseRealize

/-- **The deletion-conditioned bundle law (A.1)–(A.3), §A.1 p.10 (PDF p.11).** K. Shi, H. Sun,
*Robust Exact Realization of Pairwise Boolean Statistics*, STOC 2027 submission (manuscript sha256
62090516…): "Each of the four endpoints is uniform on V, despite their within-bundle dependence. Let
E_D mean that all endpoints avoid D. Then P(E_D) ≥ 1 − 4ε = 1023/1024 =: p∗. (A.1) […] For any
particular endpoint X of an accepted bundle, P(X = x | E_D) ≤ 1/(p∗N) < 2/N. (A.2) For a bundle C
with a = |C| ≤ 4 endpoints, let X_C = Σ_{x∈C} v_x v_xᵀ. Each endpoint is uniform before
conditioning, so E(X_C | E_D) ⪯ (a/p∗)I_m, ‖X_C‖ ≤ 4m. (A.3)" Here ε = 1/4096 and `|D| ≤ εN`.

1. For disjoint nonempty `A, B`, each of the four endpoints of a raw rectangular bundle is uniform
   on `V`: exactly a `1/N` fraction of the raw bundles has that endpoint equal to `x`.
2. For every bundle type: let a raw bundle be uniform on a finite nonempty set `Ω`, with `a ≤ 4`
   endpoints `E(ω, 0), …, E(ω, a−1)`, each uniform on `V`. If `|D| ≤ N/4096`, then (A.1) the accepted
   fraction is at least `p∗ = 1023/1024`; (A.2) for every endpoint position and every `x`, the
   accepted fraction with that endpoint equal to `x` is at most `1/(p∗N)`, and `1/(p∗N) < 2/N`;
   (A.3) the accepted average of `X_C` is `⪯ (a/p∗)I_m`, and `‖X_C‖ ≤ 4m` for every bundle
   (spectral norm).

**Formalization Note** Part 2 covers every bundle of the reserve (rectangular bundles, total triples,
coordinate edges and faces: "All bundles, including total triples, have at most four distinct
endpoints", p.12); part 1 is the uniformity that makes part 2 apply to rectangular bundles.
Probabilities are counting ratios over the uniform laws (`Ω` raw, the accepted subset conditioned).
`⪯` is the Loewner order, `B − A` positive semidefinite. -/
theorem eq_A_1_A_3_accepted_law (n : ℕ) :
    (∀ (A B : Finset (Fin n)), Disjoint A B → A.Nonempty → B.Nonempty →
      ∀ (k : Fin 4) (x : Row n),
        ((rawBundles n A B).filter fun c => endpoint c k = x).card * 2 ^ n =
          (rawBundles n A B).card) ∧
    ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (a : ℕ), a ≤ 4 → ∀ E : Ω → Fin a → Row n,
      (∀ (k : Fin a) (x : Row n),
        (Finset.univ.filter fun ω => E ω k = x).card * 2 ^ n = Fintype.card Ω) →
      ∀ D : Finset (Row n), 4096 * D.card ≤ 2 ^ n →
        let acc : Finset Ω := Finset.univ.filter fun ω => ∀ k, E ω k ∉ D
        (1023 / 1024 : ℝ) ≤ (acc.card : ℝ) / Fintype.card Ω ∧
        (∀ (k : Fin a) (x : Row n),
          ((acc.filter fun ω => E ω k = x).card : ℝ) / acc.card ≤
            1 / (1023 / 1024 * (2 : ℝ) ^ n)) ∧
        1 / (1023 / 1024 * (2 : ℝ) ^ n) < 2 / (2 : ℝ) ^ n ∧
        (((a : ℝ) / (1023 / 1024)) • (1 : Matrix (Feat n) (Feat n) ℝ) -
          ((acc.card : ℝ)⁻¹ • ∑ ω ∈ acc, Xmat n (E ω))).PosSemidef ∧
        ∀ ω, ‖Xmat n (E ω)‖ ≤ 4 * ((1 + n + n.choose 2 : ℕ) : ℝ) := by sorry

end PairwiseRealize
