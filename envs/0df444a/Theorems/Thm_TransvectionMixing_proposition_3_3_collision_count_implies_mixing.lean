-- Prove2me | Theorems.Thm_TransvectionMixing_proposition_3_3_collision_count_implies_mixing
-- name    : TransvectionMixing.proposition_3_3_collision_count_implies_mixing
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:30.8823+00:00
-- url     : https://prove2.me/theorems/503eb2bb-b6f4-44c3-b406-c4239d3ec41d
-- title:
--   Proposition 3.3 — collision count implies mixing
-- statement:
--   Let $\mathbb F_q$ be a finite field, $Y$ a finite set with $|Y|\le q^{d}$ ($d$ plays $\dim Y$), $F:\mathbb F_q^T\to Y$ a map, and $\nu=F_*\mathrm{Unif}(\mathbb F_q^T)$. Let $X^\circ\subseteq\mathbb F_q^T$ satisfy
--   $$
--   |X^\circ|\ \ge\ q^T-d(H-1)q^{T-1}\qquad\text{(as in (8))},
--   $$
--   and let $Z^\circ=\{(a,a')\in X^\circ\times X^\circ:F(a)=F(a')\}$. If $\mathcal E\ge 0$ and $|Z^\circ|\le(1+\mathcal E)q^{2T-d}$, then
--   $$
--   \|\nu-\pi_Y\|_{TV}\ \le\ \frac{d(H-1)}{2q}+\frac12\sqrt{\mathcal E+2d(H-1)q^{-1}} ,
--   $$
--   where $\pi_Y$ is the uniform law on $Y$.
--
--   This converts a Lang–Weil collision count into a total-variation bound.
--
--   **Formalization Note** $q^{T-1}$ is written $q^T/q$ and $q^{2T-d}$ is $q^{2T}/q^{d}$.
--
--   Differences from the source:
--   - generalization: F the coefficient map, Y ∈ {𝔸^𝒮, SLₙ}, X° = D(𝒥), Z° = X° ×_Y X°, with (8) and |Y(𝔽_q)| ≤ q^{dim Y} as standing facts → any map F : 𝔽_q^T → Y with Y finite, |Y| ≤ q^d, and any X° satisfying the lower bound of (8); Z° the collision pairs in X°; reason: the proof uses only these facts, which the paper's objects satisfy (p.11), so the paper's statement is an instance
--   - encoding: |Z°(𝔽_q)| → number of pairs (a, a′) ∈ X° × X° with F(a) = F(a′); reason: the 𝔽_q-points of X° ×_Y X°; same count
--   - encoding: ‖·‖_TV → the published `MarkovMixing.tvDist` (max over events of |μ(A) − ν(A)|); reason: equals ½∑|μ − ν| on probability vectors; same values
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Proposition 3.3, eqs. (8)–(11), p.11

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_TransvectionMixing_walkMat
import Definitions.Def_TransvectionMixing_HasRationalSectionSL

namespace TransvectionMixing

/-- **Proposition 3.3** (collision count implies mixing) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §3.3, p.11), in the elementary
form its proof uses. Let `q = |𝔽_q|`, let `F : 𝔽_q^T → Y` with `Y` finite and
`|Y| ≤ q^{dim Y}`, let `X° ⊆ 𝔽_q^T` with `|X°| ≥ q^T − (dim Y)(H − 1)q^{T−1}` (eq. (8)), and
let `ν = F_*Unif(𝔽_q^T)`. If `ℰ ≥ 0` and the collision count
`|Z°(𝔽_q)| = #{(a, a′) ∈ X° × X° : F(a) = F(a′)} ≤ (1 + ℰ)q^{2T − dim Y}` (eq. (9)), then
`‖ν − π_Y‖_TV ≤ (dim Y)(H − 1)/(2q) + ½√(ℰ + 2(dim Y)(H − 1)q⁻¹)` (eq. (10)).

**Formalization Note** `d` plays `dim Y`. `q^{T−1}` is `q^T/q` and `q^{2T − dim Y}` is
`q^{2T}/q^{dim Y}`, so no natural subtraction occurs. -/
theorem proposition_3_3_collision_count_implies_mixing (F : Type*) [Field F] [Fintype F]
    {Y : Type*} [Fintype Y] [DecidableEq Y] (T d H : ℕ) (Fm : (Fin T → F) → Y)
    (hY : (Fintype.card Y : ℝ) ≤ (Fintype.card F : ℝ) ^ d)
    (Xo : Finset (Fin T → F))
    (hXo : (Fintype.card F : ℝ) ^ T
        - d * ((H : ℝ) - 1) * (Fintype.card F : ℝ) ^ T / Fintype.card F ≤ Xo.card)
    (E : ℝ) (hE : 0 ≤ E)
    (hZ : (((Xo ×ˢ Xo).filter (fun p => Fm p.1 = Fm p.2)).card : ℝ)
        ≤ (1 + E) * (Fintype.card F : ℝ) ^ (2 * T) / (Fintype.card F : ℝ) ^ d) :
    MarkovMixing.tvDist (fun y => prob (fun a : Fin T → F => Fm a = y)) (unifOn Y)
      ≤ d * ((H : ℝ) - 1) / (2 * Fintype.card F)
        + 1 / 2 * Real.sqrt (E + 2 * d * ((H : ℝ) - 1) / Fintype.card F) := by sorry

end TransvectionMixing
