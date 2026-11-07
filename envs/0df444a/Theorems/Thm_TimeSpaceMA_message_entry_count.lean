-- Prove2me | Theorems.Thm_TimeSpaceMA_message_entry_count
-- name    : TimeSpaceMA.message_entry_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:59:06.098259+00:00
-- url     : https://prove2.me/theorems/e7d36c0a-334c-413b-b653-2ab5b47df7f1
-- title:
--   §3.7 — the number of table entries Merlin sends
-- statement:
--   Let $G$ be a subset-sum code with $q\ge 2$, $L\ge q$, whose distinct supports have total size at most $L$, and let $A,C,D>0$. Then:
--
--   1. at most $L^m/C$ keys $\kappa$ of $[L]^m$ satisfy $|\mathrm{sources}(\kappa)|>C$;
--   2. for $1\le j\le m-1$, the number of pairs of keys $\kappa,\kappa'$ of $[L]^{m-j}$ with $q^j|\mathrm{sources}(\kappa)||\mathrm{sources}(\kappa')|>D$ is at most $L^{2(m-j)}q^j/D\le L^{2m}/(Dq^j)$;
--   3. summing over the levels with $q^j>A$, the total is at most
--   $$\frac{L^{2m}}{D}\sum_{j:q^j>A}q^{-j}\le\frac{2L^{2m}}{AD}.$$
--
--   These counts are what bound Merlin's message length.
--
--   Differences from the source:
--   - generalization: the code of Lemma 3.10 and the protocol's thresholds A, C, D → any subset-sum code with q ≥ 2, L ≥ q and Lemma 3.10(a); any real A, C, D > 0; any m ≥ 1; reason: the argument on p.20 uses only these, and the page's values are instances
--   - encoding: "Merlin sends", "Merlin includes" → the counts of the keys and key pairs that the protocol has Merlin include; reason: the sentence on p.20 is a statement about those counts
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), §3.7, Merlin's message length, p.20; Lemma 3.23, p.19

import Definitions.Def_TimeSpaceMA_keyPairCount

namespace TimeSpaceMA

open Classical in
/-- **§3.7, Merlin's message length** (Williams, Xi, STOC 2027 submission, manuscript sha256 184c2f95…, p.20,
through Lemma 3.23, p.19). At most `L^m / C` keys `κ` have `|sources(κ)| > C`. At level `j` at most
`L^{2(m−j)} q^j / D ≤ L^{2m} / (D q^j)` pairs of keys have `q^j |sources(κ)| |sources(κ′)| > D`. Over the levels
with `q^j > A` the total is at most `(L^{2m}/D) Σ_{j : q^j > A} q^{−j} ≤ 2 L^{2m} / (A D)`.

**Formalization Note** Over any subset-sum code with `q ≥ 2`, Lemma 3.10(a) and `L ≥ q`, real `A, C, D > 0`;
levels are `1 ≤ j ≤ m − 1`. -/
theorem message_entry_count {q L m : ℕ} (hq : 2 ≤ q) (hL : q ≤ L) (hm : 1 ≤ m)
    (G : SubsetSumCode q L) (hG : distinctSize G.supp ≤ L) (A C D : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hD : 0 < D) :
    ((Finset.univ.filter fun κ : Fin m → Fin L =>
        IsKey G κ ∧ C < ((sources G κ).card : ℝ)).card : ℝ) ≤ (L : ℝ) ^ m / C ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
      (keyPairCount G m j D : ℝ) ≤ (L : ℝ) ^ (2 * (m - j)) * (q : ℝ) ^ j / D ∧
      (L : ℝ) ^ (2 * (m - j)) * (q : ℝ) ^ j / D ≤ (L : ℝ) ^ (2 * m) / (D * (q : ℝ) ^ j)) ∧
    (∑ j ∈ (Finset.Icc 1 (m - 1)).filter (fun j => A < (q : ℝ) ^ j), (keyPairCount G m j D : ℝ)) ≤
      (L : ℝ) ^ (2 * m) / D *
        ∑ j ∈ (Finset.Icc 1 (m - 1)).filter (fun j => A < (q : ℝ) ^ j), ((q : ℝ) ^ j)⁻¹ ∧
    (L : ℝ) ^ (2 * m) / D *
        ∑ j ∈ (Finset.Icc 1 (m - 1)).filter (fun j => A < (q : ℝ) ^ j), ((q : ℝ) ^ j)⁻¹ ≤
      2 * (L : ℝ) ^ (2 * m) / (A * D) := by sorry

end TimeSpaceMA
