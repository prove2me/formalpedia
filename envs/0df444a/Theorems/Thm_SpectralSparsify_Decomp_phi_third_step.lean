-- Prove2me | Theorems.Thm_SpectralSparsify_Decomp_phi_third_step
-- name    : SpectralSparsify.Decomp.phi_third_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:36.945339+00:00
-- url     : https://prove2.me/theorems/16cdad71-b15a-46c6-b3d4-7bc57924352a
-- title:
--   Proof of Theorem 7.1 — a part B − S returned at step 3 of idealDecomp (Vol(S) ≤ Vol(B)/4) has Φ^G_{B−S} ≥ φ/3
-- statement:
--   Let $G=(V,E)$ be a finite simple graph without isolated vertices and let $\varphi\le1$. Let $B\subseteq V$ be nonempty and let $S\subset B$ maximize $\operatorname{Vol}(S)$ among the proper subsets of $B$ satisfying (C.1) $\operatorname{Vol}(S)\le\operatorname{Vol}(B)/2$ and (C.2) $\Phi^G_B(S)\le\varphi$. If
--   $$\operatorname{Vol}(S)\le\tfrac14\operatorname{Vol}(B),$$
--   then
--   $$\Phi^G_{B-S}\ \ge\ \frac{\varphi}{3}.$$
--
--   In the proof of Theorem 7.1 the procedure idealDecomp returns $B-S$ as a final part exactly in this situation (its step 3); every other final part $A$ is returned at step 1 with $\Phi^G_A\ge\varphi$. This is the statement "Lemma 7.2 implies that $\Phi^G_{A_i}\ge\varphi/3$ for each $i$".
--
--   **Formalization Note** As in Lemma 7.2, the absence of isolated vertices and the nonemptiness of $B$ are hypotheses the paper leaves implicit. The procedure idealDecomp itself is not formalized; the statement isolates the property of the part returned at step 3.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 19, proof of Theorem 7.1 ("Lemma 7.2 implies that Φ^G_{A_i} ≥ φ/3 for each i"), with idealDecomp step 3

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_vol
import Definitions.Def_SpectralSparsify_Decomp_cutEdges
import Definitions.Def_SpectralSparsify_Decomp_cond

namespace SpectralSparsify.Decomp

/-- The `φ/3` step of the proof of Theorem 7.1 (arXiv:0808.4134v3, p. 19): in step 3 of
`idealDecomp(B, φ)` the part `B - S` is returned when `Vol(S) ≤ Vol(B)/4`, where `S ⊂ B`
maximizes `Vol(S)` subject to (C.1) and (C.2); Lemma 7.2 then gives `Φ^G_{B - S} ≥ φ/3`. -/
theorem phi_third_step {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) (φ : ℝ) (hφ : φ ≤ 1)
    (B S : Finset V) (hB : B.Nonempty) (hSB : S ⊂ B)
    (hC1 : vol G S ≤ vol G B / 2) (hC2 : condRel G B S ≤ φ)
    (hmax : ∀ S' : Finset V, S' ⊂ B → vol G S' ≤ vol G B / 2 → condRel G B S' ≤ φ →
      vol G S' ≤ vol G S)
    (h4 : vol G S ≤ vol G B / 4) :
    φ / 3 ≤ cond G (B \ S) := by sorry

end SpectralSparsify.Decomp
