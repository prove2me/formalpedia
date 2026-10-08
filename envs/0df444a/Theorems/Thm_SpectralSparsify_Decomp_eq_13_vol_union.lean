-- Prove2me | Theorems.Thm_SpectralSparsify_Decomp_eq_13_vol_union
-- name    : SpectralSparsify.Decomp.eq_13_vol_union
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:31.51098+00:00
-- url     : https://prove2.me/theorems/0985486f-8521-4c2e-942a-76ed35f76e67
-- title:
--   Proof of (13) — Vol(R ∪ S) ≤ ((1+α)/2) Vol(B) when Vol(R) ≤ Vol(B − S)/2 and Vol(S) = α Vol(B)
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with volumes $\operatorname{Vol}$ taken from the degrees of $G$. Let $B\subseteq V$, $S\subseteq B$ and $R\subseteq B-S$, and suppose
--   $$\operatorname{Vol}(R)\le\tfrac12\operatorname{Vol}(B-S),\qquad \operatorname{Vol}(S)=\alpha\operatorname{Vol}(B).$$
--   Then $T=R\cup S$ satisfies
--   $$\operatorname{Vol}(T)=\operatorname{Vol}(S)+\operatorname{Vol}(R)\le\Big(\frac{1+\alpha}{2}\Big)\operatorname{Vol}(B).$$
--
--   This is the computation behind (13) in the proof of Lemma 7.2: in the case $\operatorname{Vol}(T)>\operatorname{Vol}(B)/2$ it gives $\operatorname{Vol}(B-T)\ge\frac{1-\alpha}{2}\operatorname{Vol}(B)$, so that $B-T$ has volume larger than $S$.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 19, proof of Lemma 7.2, computation proving (13)

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_vol

namespace SpectralSparsify.Decomp

/-- The volume computation proving (13) (arXiv:0808.4134v3, proof of Lemma 7.2, p. 19): if
`S ⊆ B`, `R ⊆ B - S`, `Vol(R) ≤ (1/2) Vol(B - S)` and `Vol(S) = α Vol(B)`, then
`Vol(R ∪ S) ≤ ((1 + α)/2) Vol(B)`. -/
theorem eq_13_vol_union {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B S R : Finset V) (hSB : S ⊆ B) (hRB : R ⊆ B \ S)
    (hR : vol G R ≤ vol G (B \ S) / 2) (α : ℝ) (hα : vol G S = α * vol G B) :
    vol G (R ∪ S) ≤ (1 + α) / 2 * vol G B := by sorry

end SpectralSparsify.Decomp
