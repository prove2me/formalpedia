-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_lemma_5_7
-- name    : ShiAuthentication.BA.Supplement.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:25:42.345002+00:00
-- url     : https://prove2.me/theorems/e63b4429-4472-47f4-966c-ada009f2e498
-- title:
--   Lemma 5.7 — random-deletion inequality for unions of bicliques
-- statement:
--   Consider a bipartite graph with $N\ge1$ vertices on each side whose edge set is the union of complete bipartite graphs (bicliques) $L_z\times R_z$, $z$ ranging over a finite index set, with $|L_z|=|R_z|=a_z$; the bicliques may share vertices and edges. The indices are partitioned into two classes $I$ and $J$. Suppose the graph has no $k$-by-$k$ independent set, where $k\ge1$ is an integer: for every $k$-set $X$ on the left and every $k$-set $Y$ on the right some $x\in X$, $y\in Y$ are joined by an edge. Then
--   $$\frac{N^2}{4}\ \le\ \sum_{z\in I}a_z^2+k\sum_{z\in J}a_z^2+2kN\,2^{\frac{2}{N}\sum_{z\in I}a_z}.\tag{5}$$
--
--   This is a form of the random-deletion argument of Radhakrishnan and Ta-Shma; it is the counting step of the broadcast lower bound (Theorem 5.4), where large and small bicliques are charged differently.
--
--   Differences from the source:
--   - encoding: N vertices on each side; indices partitioned into I, J → both sides Fin N; a finite index type ι with I : Finset ι and J = Iᶜ; reason: a partition into two classes is exactly a subset and its complement
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Lemma 5.7, pp. 30–31

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

namespace ShiAuthentication.BA.Supplement

/-- **Lemma 5.7**, p. 30. A bipartite graph has `N ≥ 1` vertices on each side (both sides indexed
by `Fin N`) and its edge set is the union of the bicliques `L_z × R_z`, `z` ranging over a finite
index type, with `|L_z| = |R_z| = a_z` (bicliques may share vertices and edges). The indices are
partitioned into `I` and its complement `J`. If the graph has no `k`-by-`k` independent set
(`k ≥ 1`), i.e. every `k`-set `X` on the left and `k`-set `Y` on the right are joined by an
edge, then
`N²/4 ≤ Σ_{z∈I} a_z² + k Σ_{z∈J} a_z² + 2kN · 2^{(2/N) Σ_{z∈I} a_z}` (inequality (5)). -/
theorem lemma_5_7 (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (L R : ι → Finset (Fin N)) (a : ι → ℕ)
    (hL : ∀ z, (L z).card = a z) (hR : ∀ z, (R z).card = a z)
    (hind : ∀ X Y : Finset (Fin N), X.card = k → Y.card = k →
      ∃ x ∈ X, ∃ y ∈ Y, ∃ z : ι, x ∈ L z ∧ y ∈ R z) :
    (N : ℝ) ^ 2 / 4 ≤
      ∑ z ∈ I, (a z : ℝ) ^ 2 + k * ∑ z ∈ Iᶜ, (a z : ℝ) ^ 2 +
        2 * k * N * (2 : ℝ) ^ ((2 / (N : ℝ)) * ∑ z ∈ I, (a z : ℝ)) := by sorry

end ShiAuthentication.BA.Supplement
