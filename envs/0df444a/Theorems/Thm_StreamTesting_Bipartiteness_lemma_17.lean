-- Prove2me | Theorems.Thm_StreamTesting_Bipartiteness_lemma_17
-- name    : StreamTesting.Bipartiteness.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:58:08.01759+00:00
-- url     : https://prove2.me/theorems/519540dc-2de8-4f09-8c83-796cf746f759
-- title:
--   Lemma 17 — two disjoint copies preserve degree-normalized farness
-- statement:
--   Let $H$ be a finite simple graph on $m$ vertices, let $d\in\mathbb N$ and $\varepsilon_0\in\mathbb R$, and suppose that $\operatorname{del}_{\mathrm{BIP}}(H)\ge\varepsilon_0dm$. For $G_0=H\sqcup H$,
--
--   $$\operatorname{del}_{\mathrm{BIP}}(G_0)\ge\varepsilon_0d(2m).$$
--
--   This retains the same farness parameter on the doubled vertex set. It applies in particular to every base graph supplied by Lemma 15.
--
--   Differences from the source:
--   - encoding: finite simple graphs on [n], with n/2 base vertices → SimpleGraph (Fin n); base graphs on Fin m and lifts on Fin m × Bool with n = 2m; reason: zero-based relabeling preserves all graphs, unordered edges, arrival permutations, and the exact normalization
--   - generalization: the fixed connected regular high-girth far graph H of §4.1, with positive epsilon0 → any finite H and any d and real epsilon0 satisfying the same farness inequality; reason: deletion distance is additive on disjoint copies; the proof on p.41 uses only base farness, and all source instances satisfy the retained premise
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Lemma 17, printed p.21 / PDF p.21; standing model pp.3–4 and §4; proofs pp.25–26 and 40–41.

import Definitions.Def_StreamTesting_Bipartiteness_Farness
import Definitions.Def_StreamTesting_Bipartiteness_Lift

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Lemma 17, p.21; the additive farness argument needs no regularity or girth. -/
theorem lemma_17 {m : ℕ} (H : SimpleGraph (Fin m)) (d : ℕ) (ε₀ : ℝ)
    (hfar : Far H d ε₀) : Far (twoCopies H) d ε₀ := by sorry

end StreamTesting.Bipartiteness
