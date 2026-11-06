-- Prove2me | Theorems.Thm_TransvectionMixing_section_5_2_2_arbitrary_patterns
-- name    : TransvectionMixing.section_5_2_2_arbitrary_patterns
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:55.490206+00:00
-- url     : https://prove2.me/theorems/f92b23c7-ebeb-495f-ab9c-32a712b081f1
-- title:
--   §5.2.2, (29)–(30) — arbitrary patterns: conditional TV $\le\varepsilon/112$ to $\mathrm{Unif}(\mathbb F_q^{\mathcal S})$ except with probability $27\varepsilon/56$
-- statement:
--   Let $n\ge 256$, $0<|\mathcal S|<n^2/3$ and $0<\varepsilon<1$. Let $t$ be an integer with
--   $$
--   t\ \ge\ 21|\mathcal S|+89n\log n+66n\log(1/\varepsilon)\ \ (\text{when }|\mathcal S|\le n^2/10)\qquad\text{or}\qquad t\ \ge\ 37|\mathcal S|+135n\log n+100n\log(1/\varepsilon),
--   $$
--   the bounds (29) and (30) on the length of the §5.2 construction. Assume $q\ge Q_{\mathrm{geom}}(H(t,\varepsilon/14),|\mathcal S|;\varepsilon/14)$. Then for every $X\in\mathrm{SL}_n(\mathbb F_q)$,
--   $$
--   \Pr_{\sigma:|\sigma|=t}\Bigl[\bigl\|K_{\sigma,\mathcal S}(X,\cdot)-\mathrm{Unif}(\mathbb F_q^{\mathcal S})\bigr\|_{TV}>\varepsilon/112\Bigr]\ \le\ \frac{27\varepsilon}{56}.
--   $$
--   The failure probability collects collection and growth failures ($5\varepsilon/14$), burn-in and the degree bound of Lemma 3.1; on success the construction's rational section and Corollary 3.4 with $u=\varepsilon/14$ give distance at most $\varepsilon/112$.
--
--   With Lemma 3.5 this yields rows 1–2 of the main theorem's table for sparse patterns.
--
--   **Formalization Note** For $t$ beyond the schedule length the section is placed on a suffix and earlier coefficients are set to zero (proof of Theorem 1.1, p.31).
--
--   Differences from the source:
--   - reading: unnumbered output of §5.2.2 ("total failure probability at most 27ε/56 … conditional TV bound under (14)") and its use on p.31 (u = ε/14, distance ε/112, sections placed on a suffix) → for every integer t at least the applicable bound (29)/(30), every X, and q ≥ Q_geom(H(t, ε/14), |𝒮|; ε/14): Pr_σ[TV(K_{σ,𝒮}(X, ·), Unif(𝔽_q^𝒮)) > ε/112] ≤ 27ε/56; reason: the paper states this result in prose; this is its explicit content as combined in the proof of Theorem 1.1
--   - encoding: Unif(𝔽_q^𝒮) → `unifEntries`, mass q^{−|𝒮|} on every point; reason: same law
--   - encoding: laws of the walk over uniform skeletons and uniform coefficients → normalized counts (`prob`, `skelLaw`, `entryLaw`, `piS`) over finite types; reason: Lean convention for finite uniform probability; same values
--   - encoding: ‖·‖_TV → the published `MarkovMixing.tvDist` (max over events of |μ(A) − ν(A)|); reason: equals ½∑|μ − ν| on probability vectors; same values
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), §5.2.2, eqs. (29)–(30), p.24; proof of Theorem 1.1, p.31

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_TransvectionMixing_dS
import Definitions.Def_TransvectionMixing_Tshears

namespace TransvectionMixing

/-- **§5.2.2, (29)–(30)**, the output of the arbitrary-pattern construction as used in the proof
of Theorem 1.1 (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §5.2.2, p.24, and proof of Theorem 1.1, p.31). Let `n ≥ 256`,
`0 < |𝒮| < n²/3` and `0 < ε < 1`. For every integer `t` at least the applicable schedule
bound, `21|𝒮| + 89n log n + 66n log(1/ε)` when `|𝒮| ≤ n²/10` (eq. (29)) or
`37|𝒮| + 135n log n + 100n log(1/ε)` (eq. (30)), every `X ∈ SLₙ(𝔽_q)` and every field with
`q ≥ Q_geom(H(t, ε/14), |𝒮|; ε/14)` (condition (14) with `u = ε/14`), the total collection,
growth, burn-in and degree failure is at most `27ε/56`, and on success the skeleton-conditional
law is within `ε/112` of `Unif(𝔽_q^𝒮)`:
`Pr_σ[‖K_{σ,𝒮}(X, ·) − Unif(𝔽_q^𝒮)‖_TV > ε/112] ≤ 27ε/56`.

**Formalization Note** An unnumbered result; for `t` beyond the schedule the section sits on a
suffix and earlier coefficients are zero (p.31). -/
theorem section_5_2_2_arbitrary_patterns (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (hn : 256 ≤ n) (S : Finset (Fin n × Fin n)) (hS0 : S.Nonempty)
    (hS1 : (S.card : ℝ) < (n : ℝ) ^ 2 / 3) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (t : ℕ)
    (ht : ((S.card : ℝ) ≤ (n : ℝ) ^ 2 / 10 ∧
          21 * (S.card : ℝ) + 89 * n * Real.log n + 66 * n * Real.log (1 / ε) ≤ t) ∨
        37 * (S.card : ℝ) + 135 * n * Real.log n + 100 * n * Real.log (1 / ε) ≤ t)
    (hq : Qgeom (Hdeg n t (ε / 14)) S.card (ε / 14) ≤ Fintype.card F)
    (X : Matrix.SpecialLinearGroup (Fin n) F) :
    prob (fun σ : Skel n t =>
        ε / 112 < MarkovMixing.tvDist (skelLaw F σ X S) (unifEntries F S)) ≤ 27 * ε / 56 := by sorry

end TransvectionMixing
